%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1uUpgOcv54

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:54 EST 2020

% Result     : Theorem 5.92s
% Output     : Refutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 741 expanded)
%              Number of leaves         :   50 ( 239 expanded)
%              Depth                    :   22
%              Number of atoms          : 1434 (12932 expanded)
%              Number of equality atoms :   68 ( 227 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ( ( k2_partfun1 @ X53 @ X54 @ X52 @ X55 )
        = ( k7_relat_1 @ X52 @ X55 ) ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X49 @ X50 @ X48 @ X51 ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X39 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X20 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['46','55'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('63',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','38','61','62'])).

thf('64',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','38','61','62'])).

thf('66',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','60'])).

thf('69',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42
       != ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','38','61','62'])).

thf('74',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('75',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['16','19'])).

thf('77',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('78',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_E @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('84',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','60'])).

thf('85',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('88',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('92',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('95',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','95'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('97',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('98',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( ( k7_relat_1 @ sk_E @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
      | ( zip_tseitin_0 @ sk_C @ X0 )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('104',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('108',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B )
        = sk_C )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_E @ sk_B )
        = sk_C )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('116',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','60'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('117',plain,(
    ! [X56: $i] :
      ( ( v1_funct_2 @ X56 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('118',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('120',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('121',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['115','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('124',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference(clc,[status(thm)],['105','125'])).

thf('127',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['75','126'])).

thf('128',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['72','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['64','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1uUpgOcv54
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:40:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.92/6.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.92/6.12  % Solved by: fo/fo7.sh
% 5.92/6.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.92/6.12  % done 5875 iterations in 5.664s
% 5.92/6.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.92/6.12  % SZS output start Refutation
% 5.92/6.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.92/6.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.92/6.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.92/6.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.92/6.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.92/6.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.92/6.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.92/6.12  thf(sk_E_type, type, sk_E: $i).
% 5.92/6.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.92/6.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.92/6.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.92/6.12  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 5.92/6.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.92/6.12  thf(sk_B_type, type, sk_B: $i).
% 5.92/6.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.92/6.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.92/6.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.92/6.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.92/6.12  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 5.92/6.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.92/6.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.92/6.12  thf(sk_A_type, type, sk_A: $i).
% 5.92/6.12  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 5.92/6.12  thf(sk_D_type, type, sk_D: $i).
% 5.92/6.12  thf(sk_C_type, type, sk_C: $i).
% 5.92/6.12  thf(t178_funct_2, conjecture,
% 5.92/6.12    (![A:$i,B:$i,C:$i,D:$i]:
% 5.92/6.12     ( ( ~( v1_xboole_0 @ D ) ) =>
% 5.92/6.12       ( ![E:$i]:
% 5.92/6.12         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 5.92/6.12             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 5.92/6.12           ( ( ( r1_tarski @ B @ A ) & 
% 5.92/6.12               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 5.92/6.12             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 5.92/6.12               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 5.92/6.12               ( m1_subset_1 @
% 5.92/6.12                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 5.92/6.12                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 5.92/6.12  thf(zf_stmt_0, negated_conjecture,
% 5.92/6.12    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.92/6.12        ( ( ~( v1_xboole_0 @ D ) ) =>
% 5.92/6.12          ( ![E:$i]:
% 5.92/6.12            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 5.92/6.12                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 5.92/6.12              ( ( ( r1_tarski @ B @ A ) & 
% 5.92/6.12                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 5.92/6.12                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 5.92/6.12                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 5.92/6.12                  ( m1_subset_1 @
% 5.92/6.12                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 5.92/6.12                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 5.92/6.12    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 5.92/6.12  thf('0', plain,
% 5.92/6.12      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 5.92/6.12        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 5.92/6.12             sk_C)
% 5.92/6.12        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 5.92/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf('1', plain,
% 5.92/6.12      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(redefinition_k2_partfun1, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i,D:$i]:
% 5.92/6.12     ( ( ( v1_funct_1 @ C ) & 
% 5.92/6.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.92/6.12       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 5.92/6.12  thf('2', plain,
% 5.92/6.12      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 5.92/6.12         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 5.92/6.12          | ~ (v1_funct_1 @ X52)
% 5.92/6.12          | ((k2_partfun1 @ X53 @ X54 @ X52 @ X55) = (k7_relat_1 @ X52 @ X55)))),
% 5.92/6.12      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 5.92/6.12  thf('3', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 5.92/6.12          | ~ (v1_funct_1 @ sk_E))),
% 5.92/6.12      inference('sup-', [status(thm)], ['1', '2'])).
% 5.92/6.12  thf('4', plain, ((v1_funct_1 @ sk_E)),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf('5', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['3', '4'])).
% 5.92/6.12  thf('6', plain,
% 5.92/6.12      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(dt_k2_partfun1, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i,D:$i]:
% 5.92/6.12     ( ( ( v1_funct_1 @ C ) & 
% 5.92/6.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.92/6.12       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 5.92/6.12         ( m1_subset_1 @
% 5.92/6.12           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 5.92/6.12           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 5.92/6.12  thf('7', plain,
% 5.92/6.12      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 5.92/6.12         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 5.92/6.12          | ~ (v1_funct_1 @ X48)
% 5.92/6.12          | (v1_funct_1 @ (k2_partfun1 @ X49 @ X50 @ X48 @ X51)))),
% 5.92/6.12      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 5.92/6.12  thf('8', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 5.92/6.12          | ~ (v1_funct_1 @ sk_E))),
% 5.92/6.12      inference('sup-', [status(thm)], ['6', '7'])).
% 5.92/6.12  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf('10', plain,
% 5.92/6.12      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['8', '9'])).
% 5.92/6.12  thf('11', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['3', '4'])).
% 5.92/6.12  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['10', '11'])).
% 5.92/6.12  thf('13', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['3', '4'])).
% 5.92/6.12  thf('14', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['3', '4'])).
% 5.92/6.12  thf('15', plain,
% 5.92/6.12      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 5.92/6.12        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 5.92/6.12      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 5.92/6.12  thf('16', plain,
% 5.92/6.12      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf('17', plain,
% 5.92/6.12      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(redefinition_k7_relset_1, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i,D:$i]:
% 5.92/6.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.92/6.12       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 5.92/6.12  thf('18', plain,
% 5.92/6.12      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 5.92/6.12         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 5.92/6.12          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 5.92/6.12      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 5.92/6.12  thf('19', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('sup-', [status(thm)], ['17', '18'])).
% 5.92/6.12  thf('20', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 5.92/6.12      inference('demod', [status(thm)], ['16', '19'])).
% 5.92/6.12  thf(t148_relat_1, axiom,
% 5.92/6.12    (![A:$i,B:$i]:
% 5.92/6.12     ( ( v1_relat_1 @ B ) =>
% 5.92/6.12       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 5.92/6.12  thf('21', plain,
% 5.92/6.12      (![X23 : $i, X24 : $i]:
% 5.92/6.12         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 5.92/6.12          | ~ (v1_relat_1 @ X23))),
% 5.92/6.12      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.92/6.12  thf(d10_xboole_0, axiom,
% 5.92/6.12    (![A:$i,B:$i]:
% 5.92/6.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.92/6.12  thf('22', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.92/6.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.92/6.12  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.92/6.12      inference('simplify', [status(thm)], ['22'])).
% 5.92/6.12  thf(t11_relset_1, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i]:
% 5.92/6.12     ( ( v1_relat_1 @ C ) =>
% 5.92/6.12       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 5.92/6.12           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 5.92/6.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 5.92/6.12  thf('24', plain,
% 5.92/6.12      (![X37 : $i, X38 : $i, X39 : $i]:
% 5.92/6.12         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 5.92/6.12          | ~ (r1_tarski @ (k2_relat_1 @ X37) @ X39)
% 5.92/6.12          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 5.92/6.12          | ~ (v1_relat_1 @ X37))),
% 5.92/6.12      inference('cnf', [status(esa)], [t11_relset_1])).
% 5.92/6.12  thf('25', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i]:
% 5.92/6.12         (~ (v1_relat_1 @ X0)
% 5.92/6.12          | (m1_subset_1 @ X0 @ 
% 5.92/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 5.92/6.12          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 5.92/6.12      inference('sup-', [status(thm)], ['23', '24'])).
% 5.92/6.12  thf('26', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.12         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 5.92/6.12          | ~ (v1_relat_1 @ X1)
% 5.92/6.12          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 5.92/6.12             (k1_zfmisc_1 @ 
% 5.92/6.12              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)))
% 5.92/6.12          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['21', '25'])).
% 5.92/6.12  thf('27', plain,
% 5.92/6.12      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 5.92/6.12        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12           (k1_zfmisc_1 @ 
% 5.92/6.12            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 5.92/6.12        | ~ (v1_relat_1 @ sk_E))),
% 5.92/6.12      inference('sup-', [status(thm)], ['20', '26'])).
% 5.92/6.12  thf('28', plain,
% 5.92/6.12      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(cc2_relset_1, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i]:
% 5.92/6.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.92/6.12       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.92/6.12  thf('29', plain,
% 5.92/6.12      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.92/6.12         ((v4_relat_1 @ X27 @ X28)
% 5.92/6.12          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 5.92/6.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.92/6.12  thf('30', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 5.92/6.12      inference('sup-', [status(thm)], ['28', '29'])).
% 5.92/6.12  thf(fc23_relat_1, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i]:
% 5.92/6.12     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 5.92/6.12       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 5.92/6.12         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 5.92/6.12         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 5.92/6.12  thf('31', plain,
% 5.92/6.12      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.92/6.12         ((v1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 5.92/6.12          | ~ (v4_relat_1 @ X18 @ X20)
% 5.92/6.12          | ~ (v1_relat_1 @ X18))),
% 5.92/6.12      inference('cnf', [status(esa)], [fc23_relat_1])).
% 5.92/6.12  thf('32', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (~ (v1_relat_1 @ sk_E) | (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['30', '31'])).
% 5.92/6.12  thf('33', plain,
% 5.92/6.12      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(cc2_relat_1, axiom,
% 5.92/6.12    (![A:$i]:
% 5.92/6.12     ( ( v1_relat_1 @ A ) =>
% 5.92/6.12       ( ![B:$i]:
% 5.92/6.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.92/6.12  thf('34', plain,
% 5.92/6.12      (![X14 : $i, X15 : $i]:
% 5.92/6.12         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 5.92/6.12          | (v1_relat_1 @ X14)
% 5.92/6.12          | ~ (v1_relat_1 @ X15))),
% 5.92/6.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.92/6.12  thf('35', plain,
% 5.92/6.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 5.92/6.12      inference('sup-', [status(thm)], ['33', '34'])).
% 5.92/6.12  thf(fc6_relat_1, axiom,
% 5.92/6.12    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.92/6.12  thf('36', plain,
% 5.92/6.12      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 5.92/6.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.92/6.12  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 5.92/6.12      inference('demod', [status(thm)], ['35', '36'])).
% 5.92/6.12  thf('38', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['32', '37'])).
% 5.92/6.12  thf('39', plain, ((r1_tarski @ sk_B @ sk_A)),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf('40', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(d1_funct_2, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i]:
% 5.92/6.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.92/6.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.92/6.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.92/6.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.92/6.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.92/6.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.92/6.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.92/6.12  thf(zf_stmt_1, axiom,
% 5.92/6.12    (![C:$i,B:$i,A:$i]:
% 5.92/6.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.92/6.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.92/6.12  thf('41', plain,
% 5.92/6.12      (![X42 : $i, X43 : $i, X44 : $i]:
% 5.92/6.12         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 5.92/6.12          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 5.92/6.12          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.12  thf('42', plain,
% 5.92/6.12      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 5.92/6.12        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['40', '41'])).
% 5.92/6.12  thf('43', plain,
% 5.92/6.12      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(redefinition_k1_relset_1, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i]:
% 5.92/6.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.92/6.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.92/6.12  thf('44', plain,
% 5.92/6.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.92/6.12         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 5.92/6.12          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 5.92/6.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.92/6.12  thf('45', plain,
% 5.92/6.12      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 5.92/6.12      inference('sup-', [status(thm)], ['43', '44'])).
% 5.92/6.12  thf('46', plain,
% 5.92/6.12      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_E)))),
% 5.92/6.12      inference('demod', [status(thm)], ['42', '45'])).
% 5.92/6.12  thf(zf_stmt_2, axiom,
% 5.92/6.12    (![B:$i,A:$i]:
% 5.92/6.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.92/6.12       ( zip_tseitin_0 @ B @ A ) ))).
% 5.92/6.12  thf('47', plain,
% 5.92/6.12      (![X40 : $i, X41 : $i]:
% 5.92/6.12         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.92/6.12  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.92/6.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.92/6.12  thf('49', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.92/6.12      inference('sup+', [status(thm)], ['47', '48'])).
% 5.92/6.12  thf('50', plain,
% 5.92/6.12      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.92/6.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.92/6.12  thf(zf_stmt_5, axiom,
% 5.92/6.12    (![A:$i,B:$i,C:$i]:
% 5.92/6.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.92/6.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.92/6.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.92/6.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.92/6.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.92/6.12  thf('51', plain,
% 5.92/6.12      (![X45 : $i, X46 : $i, X47 : $i]:
% 5.92/6.12         (~ (zip_tseitin_0 @ X45 @ X46)
% 5.92/6.12          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 5.92/6.12          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.92/6.12  thf('52', plain,
% 5.92/6.12      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 5.92/6.12      inference('sup-', [status(thm)], ['50', '51'])).
% 5.92/6.12  thf('53', plain,
% 5.92/6.12      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 5.92/6.12      inference('sup-', [status(thm)], ['49', '52'])).
% 5.92/6.12  thf('54', plain, (~ (v1_xboole_0 @ sk_D)),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf('55', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 5.92/6.12      inference('clc', [status(thm)], ['53', '54'])).
% 5.92/6.12  thf('56', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 5.92/6.12      inference('demod', [status(thm)], ['46', '55'])).
% 5.92/6.12  thf(t91_relat_1, axiom,
% 5.92/6.12    (![A:$i,B:$i]:
% 5.92/6.12     ( ( v1_relat_1 @ B ) =>
% 5.92/6.12       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 5.92/6.12         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 5.92/6.12  thf('57', plain,
% 5.92/6.12      (![X25 : $i, X26 : $i]:
% 5.92/6.12         (~ (r1_tarski @ X25 @ (k1_relat_1 @ X26))
% 5.92/6.12          | ((k1_relat_1 @ (k7_relat_1 @ X26 @ X25)) = (X25))
% 5.92/6.12          | ~ (v1_relat_1 @ X26))),
% 5.92/6.12      inference('cnf', [status(esa)], [t91_relat_1])).
% 5.92/6.12  thf('58', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (~ (r1_tarski @ X0 @ sk_A)
% 5.92/6.12          | ~ (v1_relat_1 @ sk_E)
% 5.92/6.12          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['56', '57'])).
% 5.92/6.12  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 5.92/6.12      inference('demod', [status(thm)], ['35', '36'])).
% 5.92/6.12  thf('60', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (~ (r1_tarski @ X0 @ sk_A)
% 5.92/6.12          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 5.92/6.12      inference('demod', [status(thm)], ['58', '59'])).
% 5.92/6.12  thf('61', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 5.92/6.12      inference('sup-', [status(thm)], ['39', '60'])).
% 5.92/6.12  thf('62', plain, ((v1_relat_1 @ sk_E)),
% 5.92/6.12      inference('demod', [status(thm)], ['35', '36'])).
% 5.92/6.12  thf('63', plain,
% 5.92/6.12      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.92/6.12      inference('demod', [status(thm)], ['27', '38', '61', '62'])).
% 5.92/6.12  thf('64', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 5.92/6.12      inference('demod', [status(thm)], ['15', '63'])).
% 5.92/6.12  thf('65', plain,
% 5.92/6.12      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.92/6.12      inference('demod', [status(thm)], ['27', '38', '61', '62'])).
% 5.92/6.12  thf('66', plain,
% 5.92/6.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.92/6.12         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 5.92/6.12          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 5.92/6.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.92/6.12  thf('67', plain,
% 5.92/6.12      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 5.92/6.12         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['65', '66'])).
% 5.92/6.12  thf('68', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 5.92/6.12      inference('sup-', [status(thm)], ['39', '60'])).
% 5.92/6.12  thf('69', plain,
% 5.92/6.12      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 5.92/6.12      inference('demod', [status(thm)], ['67', '68'])).
% 5.92/6.12  thf('70', plain,
% 5.92/6.12      (![X42 : $i, X43 : $i, X44 : $i]:
% 5.92/6.12         (((X42) != (k1_relset_1 @ X42 @ X43 @ X44))
% 5.92/6.12          | (v1_funct_2 @ X44 @ X42 @ X43)
% 5.92/6.12          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.92/6.12  thf('71', plain,
% 5.92/6.12      ((((sk_B) != (sk_B))
% 5.92/6.12        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 5.92/6.12        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 5.92/6.12      inference('sup-', [status(thm)], ['69', '70'])).
% 5.92/6.12  thf('72', plain,
% 5.92/6.12      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 5.92/6.12        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 5.92/6.12      inference('simplify', [status(thm)], ['71'])).
% 5.92/6.12  thf('73', plain,
% 5.92/6.12      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 5.92/6.12      inference('demod', [status(thm)], ['27', '38', '61', '62'])).
% 5.92/6.12  thf('74', plain,
% 5.92/6.12      (![X45 : $i, X46 : $i, X47 : $i]:
% 5.92/6.12         (~ (zip_tseitin_0 @ X45 @ X46)
% 5.92/6.12          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 5.92/6.12          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.92/6.12  thf('75', plain,
% 5.92/6.12      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 5.92/6.12        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 5.92/6.12      inference('sup-', [status(thm)], ['73', '74'])).
% 5.92/6.12  thf('76', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 5.92/6.12      inference('demod', [status(thm)], ['16', '19'])).
% 5.92/6.12  thf('77', plain,
% 5.92/6.12      (![X40 : $i, X41 : $i]:
% 5.92/6.12         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.12  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.92/6.12  thf('78', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.92/6.12      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.92/6.12  thf('79', plain,
% 5.92/6.12      (![X0 : $i, X2 : $i]:
% 5.92/6.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.92/6.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.92/6.12  thf('80', plain,
% 5.92/6.12      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['78', '79'])).
% 5.92/6.12  thf('81', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.12         (~ (r1_tarski @ X1 @ X0)
% 5.92/6.12          | (zip_tseitin_0 @ X0 @ X2)
% 5.92/6.12          | ((X1) = (k1_xboole_0)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['77', '80'])).
% 5.92/6.12  thf('82', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (((k9_relat_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 5.92/6.12          | (zip_tseitin_0 @ sk_C @ X0))),
% 5.92/6.12      inference('sup-', [status(thm)], ['76', '81'])).
% 5.92/6.12  thf('83', plain,
% 5.92/6.12      (![X23 : $i, X24 : $i]:
% 5.92/6.12         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 5.92/6.12          | ~ (v1_relat_1 @ X23))),
% 5.92/6.12      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.92/6.12  thf('84', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 5.92/6.12      inference('sup-', [status(thm)], ['39', '60'])).
% 5.92/6.12  thf('85', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.92/6.12      inference('simplify', [status(thm)], ['22'])).
% 5.92/6.12  thf('86', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i]:
% 5.92/6.12         (~ (v1_relat_1 @ X0)
% 5.92/6.12          | (m1_subset_1 @ X0 @ 
% 5.92/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 5.92/6.12          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 5.92/6.12      inference('sup-', [status(thm)], ['23', '24'])).
% 5.92/6.12  thf('87', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((m1_subset_1 @ X0 @ 
% 5.92/6.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 5.92/6.12          | ~ (v1_relat_1 @ X0))),
% 5.92/6.12      inference('sup-', [status(thm)], ['85', '86'])).
% 5.92/6.12  thf(t3_subset, axiom,
% 5.92/6.12    (![A:$i,B:$i]:
% 5.92/6.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.92/6.12  thf('88', plain,
% 5.92/6.12      (![X8 : $i, X9 : $i]:
% 5.92/6.12         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 5.92/6.12      inference('cnf', [status(esa)], [t3_subset])).
% 5.92/6.12  thf('89', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (~ (v1_relat_1 @ X0)
% 5.92/6.12          | (r1_tarski @ X0 @ 
% 5.92/6.12             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 5.92/6.12      inference('sup-', [status(thm)], ['87', '88'])).
% 5.92/6.12  thf('90', plain,
% 5.92/6.12      (((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))))
% 5.92/6.12        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 5.92/6.12      inference('sup+', [status(thm)], ['84', '89'])).
% 5.92/6.12  thf('91', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['32', '37'])).
% 5.92/6.12  thf('92', plain,
% 5.92/6.12      ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12        (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))))),
% 5.92/6.12      inference('demod', [status(thm)], ['90', '91'])).
% 5.92/6.12  thf('93', plain,
% 5.92/6.12      (((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12         (k2_zfmisc_1 @ sk_B @ (k9_relat_1 @ sk_E @ sk_B)))
% 5.92/6.12        | ~ (v1_relat_1 @ sk_E))),
% 5.92/6.12      inference('sup+', [status(thm)], ['83', '92'])).
% 5.92/6.12  thf('94', plain, ((v1_relat_1 @ sk_E)),
% 5.92/6.12      inference('demod', [status(thm)], ['35', '36'])).
% 5.92/6.12  thf('95', plain,
% 5.92/6.12      ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12        (k2_zfmisc_1 @ sk_B @ (k9_relat_1 @ sk_E @ sk_B)))),
% 5.92/6.12      inference('demod', [status(thm)], ['93', '94'])).
% 5.92/6.12  thf('96', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12           (k2_zfmisc_1 @ sk_B @ k1_xboole_0))
% 5.92/6.12          | (zip_tseitin_0 @ sk_C @ X0))),
% 5.92/6.12      inference('sup+', [status(thm)], ['82', '95'])).
% 5.92/6.12  thf(t113_zfmisc_1, axiom,
% 5.92/6.12    (![A:$i,B:$i]:
% 5.92/6.12     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.92/6.12       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.92/6.12  thf('97', plain,
% 5.92/6.12      (![X5 : $i, X6 : $i]:
% 5.92/6.12         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 5.92/6.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.92/6.12  thf('98', plain,
% 5.92/6.12      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 5.92/6.12      inference('simplify', [status(thm)], ['97'])).
% 5.92/6.12  thf('99', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ k1_xboole_0)
% 5.92/6.12          | (zip_tseitin_0 @ sk_C @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['96', '98'])).
% 5.92/6.12  thf('100', plain,
% 5.92/6.12      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['78', '79'])).
% 5.92/6.12  thf('101', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((zip_tseitin_0 @ sk_C @ X0)
% 5.92/6.12          | ((k7_relat_1 @ sk_E @ sk_B) = (k1_xboole_0)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['99', '100'])).
% 5.92/6.12  thf('102', plain,
% 5.92/6.12      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 5.92/6.12        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 5.92/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 5.92/6.12      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 5.92/6.12  thf('103', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 5.92/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 5.92/6.12          | (zip_tseitin_0 @ sk_C @ X0)
% 5.92/6.12          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 5.92/6.12      inference('sup-', [status(thm)], ['101', '102'])).
% 5.92/6.12  thf(t4_subset_1, axiom,
% 5.92/6.12    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.92/6.12  thf('104', plain,
% 5.92/6.12      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.92/6.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.92/6.12  thf('105', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((zip_tseitin_0 @ sk_C @ X0)
% 5.92/6.12          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 5.92/6.12      inference('demod', [status(thm)], ['103', '104'])).
% 5.92/6.12  thf('106', plain,
% 5.92/6.12      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.92/6.12  thf('107', plain,
% 5.92/6.12      (![X40 : $i, X41 : $i]:
% 5.92/6.12         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 5.92/6.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.92/6.12  thf('108', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 5.92/6.12      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.92/6.12  thf('109', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.12         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 5.92/6.12      inference('sup+', [status(thm)], ['107', '108'])).
% 5.92/6.12  thf('110', plain,
% 5.92/6.12      (![X0 : $i, X2 : $i]:
% 5.92/6.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.92/6.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.92/6.12  thf('111', plain,
% 5.92/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.92/6.12         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 5.92/6.12      inference('sup-', [status(thm)], ['109', '110'])).
% 5.92/6.12  thf('112', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (((k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) = (sk_C))
% 5.92/6.12          | (zip_tseitin_0 @ sk_C @ X0))),
% 5.92/6.12      inference('sup-', [status(thm)], ['106', '111'])).
% 5.92/6.12  thf('113', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('sup-', [status(thm)], ['17', '18'])).
% 5.92/6.12  thf('114', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         (((k9_relat_1 @ sk_E @ sk_B) = (sk_C)) | (zip_tseitin_0 @ sk_C @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['112', '113'])).
% 5.92/6.12  thf('115', plain,
% 5.92/6.12      (![X23 : $i, X24 : $i]:
% 5.92/6.12         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 5.92/6.12          | ~ (v1_relat_1 @ X23))),
% 5.92/6.12      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.92/6.12  thf('116', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 5.92/6.12      inference('sup-', [status(thm)], ['39', '60'])).
% 5.92/6.12  thf(t3_funct_2, axiom,
% 5.92/6.12    (![A:$i]:
% 5.92/6.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.92/6.12       ( ( v1_funct_1 @ A ) & 
% 5.92/6.12         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 5.92/6.12         ( m1_subset_1 @
% 5.92/6.12           A @ 
% 5.92/6.12           ( k1_zfmisc_1 @
% 5.92/6.12             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.92/6.12  thf('117', plain,
% 5.92/6.12      (![X56 : $i]:
% 5.92/6.12         ((v1_funct_2 @ X56 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))
% 5.92/6.12          | ~ (v1_funct_1 @ X56)
% 5.92/6.12          | ~ (v1_relat_1 @ X56))),
% 5.92/6.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 5.92/6.12  thf('118', plain,
% 5.92/6.12      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ 
% 5.92/6.12         (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))
% 5.92/6.12        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 5.92/6.12        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 5.92/6.12      inference('sup+', [status(thm)], ['116', '117'])).
% 5.92/6.12  thf('119', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['32', '37'])).
% 5.92/6.12  thf('120', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 5.92/6.12      inference('demod', [status(thm)], ['10', '11'])).
% 5.92/6.12  thf('121', plain,
% 5.92/6.12      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ 
% 5.92/6.12        (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 5.92/6.12      inference('demod', [status(thm)], ['118', '119', '120'])).
% 5.92/6.12  thf('122', plain,
% 5.92/6.12      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ 
% 5.92/6.12         (k9_relat_1 @ sk_E @ sk_B))
% 5.92/6.12        | ~ (v1_relat_1 @ sk_E))),
% 5.92/6.12      inference('sup+', [status(thm)], ['115', '121'])).
% 5.92/6.12  thf('123', plain, ((v1_relat_1 @ sk_E)),
% 5.92/6.12      inference('demod', [status(thm)], ['35', '36'])).
% 5.92/6.12  thf('124', plain,
% 5.92/6.12      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ 
% 5.92/6.12        (k9_relat_1 @ sk_E @ sk_B))),
% 5.92/6.12      inference('demod', [status(thm)], ['122', '123'])).
% 5.92/6.12  thf('125', plain,
% 5.92/6.12      (![X0 : $i]:
% 5.92/6.12         ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 5.92/6.12          | (zip_tseitin_0 @ sk_C @ X0))),
% 5.92/6.12      inference('sup+', [status(thm)], ['114', '124'])).
% 5.92/6.12  thf('126', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 5.92/6.12      inference('clc', [status(thm)], ['105', '125'])).
% 5.92/6.12  thf('127', plain,
% 5.92/6.12      ((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 5.92/6.12      inference('demod', [status(thm)], ['75', '126'])).
% 5.92/6.12  thf('128', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 5.92/6.12      inference('demod', [status(thm)], ['72', '127'])).
% 5.92/6.12  thf('129', plain, ($false), inference('demod', [status(thm)], ['64', '128'])).
% 5.92/6.12  
% 5.92/6.12  % SZS output end Refutation
% 5.92/6.12  
% 5.92/6.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
