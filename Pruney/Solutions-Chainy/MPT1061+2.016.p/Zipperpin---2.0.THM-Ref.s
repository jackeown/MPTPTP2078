%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rfsx7Irf7f

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:54 EST 2020

% Result     : Theorem 25.31s
% Output     : Refutation 25.31s
% Verified   : 
% Statistics : Number of formulae       :  213 (5048 expanded)
%              Number of leaves         :   50 (1514 expanded)
%              Depth                    :   19
%              Number of atoms          : 1594 (92308 expanded)
%              Number of equality atoms :   92 (1714 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ( ( k2_partfun1 @ X50 @ X51 @ X49 @ X52 )
        = ( k7_relat_1 @ X49 @ X52 ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X36 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['61','62'])).

thf('67',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','38','65','66'])).

thf('68',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','67'])).

thf('69',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','38','65','66'])).

thf('71',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','38','65','66'])).

thf('75',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('76',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','64'])).

thf('78',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39
       != ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('80',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','67'])).

thf('83',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','64'])).

thf('87',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['39','64'])).

thf('94',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('95',plain,
    ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','38','65','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('97',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','83'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('102',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('103',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('104',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('105',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','83'])).

thf('106',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','103','104','105','106'])).

thf('108',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','103','104','105','106'])).

thf('109',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('116',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('120',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('122',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','122'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('124',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['120','121'])).

thf('127',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','131'])).

thf('133',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['95','107','108','132'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('134',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('135',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('137',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('139',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('143',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['61','62'])).

thf('146',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('148',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['95','107','108','132'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','131'])).

thf('151',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39
       != ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('155',plain,(
    ! [X37: $i] :
      ( zip_tseitin_0 @ X37 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('157',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['153','159'])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['85','133','148','149','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rfsx7Irf7f
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 25.31/25.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 25.31/25.56  % Solved by: fo/fo7.sh
% 25.31/25.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.31/25.56  % done 13644 iterations in 25.094s
% 25.31/25.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 25.31/25.56  % SZS output start Refutation
% 25.31/25.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 25.31/25.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 25.31/25.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 25.31/25.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 25.31/25.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 25.31/25.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 25.31/25.56  thf(sk_B_type, type, sk_B: $i).
% 25.31/25.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 25.31/25.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 25.31/25.56  thf(sk_A_type, type, sk_A: $i).
% 25.31/25.56  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 25.31/25.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 25.31/25.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 25.31/25.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 25.31/25.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 25.31/25.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 25.31/25.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 25.31/25.56  thf(sk_E_type, type, sk_E: $i).
% 25.31/25.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 25.31/25.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 25.31/25.56  thf(sk_D_type, type, sk_D: $i).
% 25.31/25.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 25.31/25.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 25.31/25.56  thf(sk_C_type, type, sk_C: $i).
% 25.31/25.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 25.31/25.56  thf(t178_funct_2, conjecture,
% 25.31/25.56    (![A:$i,B:$i,C:$i,D:$i]:
% 25.31/25.56     ( ( ~( v1_xboole_0 @ D ) ) =>
% 25.31/25.56       ( ![E:$i]:
% 25.31/25.56         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 25.31/25.56             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 25.31/25.56           ( ( ( r1_tarski @ B @ A ) & 
% 25.31/25.56               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 25.31/25.56             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 25.31/25.56               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 25.31/25.56               ( m1_subset_1 @
% 25.31/25.56                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 25.31/25.56                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 25.31/25.56  thf(zf_stmt_0, negated_conjecture,
% 25.31/25.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 25.31/25.56        ( ( ~( v1_xboole_0 @ D ) ) =>
% 25.31/25.56          ( ![E:$i]:
% 25.31/25.56            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 25.31/25.56                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 25.31/25.56              ( ( ( r1_tarski @ B @ A ) & 
% 25.31/25.56                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 25.31/25.56                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 25.31/25.56                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 25.31/25.56                  ( m1_subset_1 @
% 25.31/25.56                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 25.31/25.56                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 25.31/25.56    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 25.31/25.56  thf('0', plain,
% 25.31/25.56      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 25.31/25.56        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 25.31/25.56             sk_C)
% 25.31/25.56        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 25.31/25.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('1', plain,
% 25.31/25.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf(redefinition_k2_partfun1, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i,D:$i]:
% 25.31/25.56     ( ( ( v1_funct_1 @ C ) & 
% 25.31/25.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 25.31/25.56       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 25.31/25.56  thf('2', plain,
% 25.31/25.56      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 25.31/25.56         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 25.31/25.56          | ~ (v1_funct_1 @ X49)
% 25.31/25.56          | ((k2_partfun1 @ X50 @ X51 @ X49 @ X52) = (k7_relat_1 @ X49 @ X52)))),
% 25.31/25.56      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 25.31/25.56  thf('3', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 25.31/25.56          | ~ (v1_funct_1 @ sk_E))),
% 25.31/25.56      inference('sup-', [status(thm)], ['1', '2'])).
% 25.31/25.56  thf('4', plain, ((v1_funct_1 @ sk_E)),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('5', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['3', '4'])).
% 25.31/25.56  thf('6', plain,
% 25.31/25.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf(dt_k2_partfun1, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i,D:$i]:
% 25.31/25.56     ( ( ( v1_funct_1 @ C ) & 
% 25.31/25.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 25.31/25.56       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 25.31/25.56         ( m1_subset_1 @
% 25.31/25.56           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 25.31/25.56           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 25.31/25.56  thf('7', plain,
% 25.31/25.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 25.31/25.56         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 25.31/25.56          | ~ (v1_funct_1 @ X45)
% 25.31/25.56          | (v1_funct_1 @ (k2_partfun1 @ X46 @ X47 @ X45 @ X48)))),
% 25.31/25.56      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 25.31/25.56  thf('8', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 25.31/25.56          | ~ (v1_funct_1 @ sk_E))),
% 25.31/25.56      inference('sup-', [status(thm)], ['6', '7'])).
% 25.31/25.56  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('10', plain,
% 25.31/25.56      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['8', '9'])).
% 25.31/25.56  thf('11', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['3', '4'])).
% 25.31/25.56  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['10', '11'])).
% 25.31/25.56  thf('13', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['3', '4'])).
% 25.31/25.56  thf('14', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['3', '4'])).
% 25.31/25.56  thf('15', plain,
% 25.31/25.56      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 25.31/25.56        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 25.31/25.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 25.31/25.56      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 25.31/25.56  thf('16', plain,
% 25.31/25.56      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('17', plain,
% 25.31/25.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf(redefinition_k7_relset_1, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i,D:$i]:
% 25.31/25.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.31/25.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 25.31/25.56  thf('18', plain,
% 25.31/25.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 25.31/25.56         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 25.31/25.56          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 25.31/25.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 25.31/25.56  thf('19', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['17', '18'])).
% 25.31/25.56  thf('20', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 25.31/25.56      inference('demod', [status(thm)], ['16', '19'])).
% 25.31/25.56  thf(t148_relat_1, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( v1_relat_1 @ B ) =>
% 25.31/25.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 25.31/25.56  thf('21', plain,
% 25.31/25.56      (![X16 : $i, X17 : $i]:
% 25.31/25.56         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 25.31/25.56          | ~ (v1_relat_1 @ X16))),
% 25.31/25.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 25.31/25.56  thf(d10_xboole_0, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 25.31/25.56  thf('22', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 25.31/25.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.31/25.56  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 25.31/25.56      inference('simplify', [status(thm)], ['22'])).
% 25.31/25.56  thf(t11_relset_1, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i]:
% 25.31/25.56     ( ( v1_relat_1 @ C ) =>
% 25.31/25.56       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 25.31/25.56           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 25.31/25.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 25.31/25.56  thf('24', plain,
% 25.31/25.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 25.31/25.56         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 25.31/25.56          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ X36)
% 25.31/25.56          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 25.31/25.56          | ~ (v1_relat_1 @ X34))),
% 25.31/25.56      inference('cnf', [status(esa)], [t11_relset_1])).
% 25.31/25.56  thf('25', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]:
% 25.31/25.56         (~ (v1_relat_1 @ X0)
% 25.31/25.56          | (m1_subset_1 @ X0 @ 
% 25.31/25.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 25.31/25.56          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 25.31/25.56      inference('sup-', [status(thm)], ['23', '24'])).
% 25.31/25.56  thf('26', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.31/25.56         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 25.31/25.56          | ~ (v1_relat_1 @ X1)
% 25.31/25.56          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 25.31/25.56             (k1_zfmisc_1 @ 
% 25.31/25.56              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)))
% 25.31/25.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['21', '25'])).
% 25.31/25.56  thf('27', plain,
% 25.31/25.56      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 25.31/25.56        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 25.31/25.56           (k1_zfmisc_1 @ 
% 25.31/25.56            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 25.31/25.56        | ~ (v1_relat_1 @ sk_E))),
% 25.31/25.56      inference('sup-', [status(thm)], ['20', '26'])).
% 25.31/25.56  thf('28', plain,
% 25.31/25.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('29', plain,
% 25.31/25.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 25.31/25.56         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 25.31/25.56          | ~ (v1_funct_1 @ X45)
% 25.31/25.56          | (m1_subset_1 @ (k2_partfun1 @ X46 @ X47 @ X45 @ X48) @ 
% 25.31/25.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 25.31/25.56      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 25.31/25.56  thf('30', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 25.31/25.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 25.31/25.56          | ~ (v1_funct_1 @ sk_E))),
% 25.31/25.56      inference('sup-', [status(thm)], ['28', '29'])).
% 25.31/25.56  thf('31', plain, ((v1_funct_1 @ sk_E)),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('32', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 25.31/25.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('demod', [status(thm)], ['30', '31'])).
% 25.31/25.56  thf('33', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['3', '4'])).
% 25.31/25.56  thf('34', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 25.31/25.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('demod', [status(thm)], ['32', '33'])).
% 25.31/25.56  thf(cc2_relat_1, axiom,
% 25.31/25.56    (![A:$i]:
% 25.31/25.56     ( ( v1_relat_1 @ A ) =>
% 25.31/25.56       ( ![B:$i]:
% 25.31/25.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 25.31/25.56  thf('35', plain,
% 25.31/25.56      (![X10 : $i, X11 : $i]:
% 25.31/25.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 25.31/25.56          | (v1_relat_1 @ X10)
% 25.31/25.56          | ~ (v1_relat_1 @ X11))),
% 25.31/25.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 25.31/25.56  thf('36', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 25.31/25.56          | (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['34', '35'])).
% 25.31/25.56  thf(fc6_relat_1, axiom,
% 25.31/25.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 25.31/25.56  thf('37', plain,
% 25.31/25.56      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 25.31/25.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 25.31/25.56  thf('38', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['36', '37'])).
% 25.31/25.56  thf('39', plain, ((r1_tarski @ sk_B @ sk_A)),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('40', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf(d1_funct_2, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i]:
% 25.31/25.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.31/25.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 25.31/25.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 25.31/25.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 25.31/25.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 25.31/25.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 25.31/25.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 25.31/25.56  thf(zf_stmt_1, axiom,
% 25.31/25.56    (![C:$i,B:$i,A:$i]:
% 25.31/25.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 25.31/25.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 25.31/25.56  thf('41', plain,
% 25.31/25.56      (![X39 : $i, X40 : $i, X41 : $i]:
% 25.31/25.56         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 25.31/25.56          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 25.31/25.56          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.31/25.56  thf('42', plain,
% 25.31/25.56      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 25.31/25.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['40', '41'])).
% 25.31/25.56  thf('43', plain,
% 25.31/25.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf(redefinition_k1_relset_1, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i]:
% 25.31/25.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.31/25.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 25.31/25.56  thf('44', plain,
% 25.31/25.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 25.31/25.56         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 25.31/25.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 25.31/25.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 25.31/25.56  thf('45', plain,
% 25.31/25.56      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 25.31/25.56      inference('sup-', [status(thm)], ['43', '44'])).
% 25.31/25.56  thf('46', plain,
% 25.31/25.56      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_E)))),
% 25.31/25.56      inference('demod', [status(thm)], ['42', '45'])).
% 25.31/25.56  thf(zf_stmt_2, axiom,
% 25.31/25.56    (![B:$i,A:$i]:
% 25.31/25.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 25.31/25.56       ( zip_tseitin_0 @ B @ A ) ))).
% 25.31/25.56  thf('47', plain,
% 25.31/25.56      (![X37 : $i, X38 : $i]:
% 25.31/25.56         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.31/25.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 25.31/25.56  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 25.31/25.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 25.31/25.56  thf('49', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 25.31/25.56      inference('sup+', [status(thm)], ['47', '48'])).
% 25.31/25.56  thf('50', plain,
% 25.31/25.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 25.31/25.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 25.31/25.56  thf(zf_stmt_5, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i]:
% 25.31/25.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.31/25.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 25.31/25.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 25.31/25.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 25.31/25.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 25.31/25.56  thf('51', plain,
% 25.31/25.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 25.31/25.56         (~ (zip_tseitin_0 @ X42 @ X43)
% 25.31/25.56          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 25.31/25.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.31/25.56  thf('52', plain,
% 25.31/25.56      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 25.31/25.56      inference('sup-', [status(thm)], ['50', '51'])).
% 25.31/25.56  thf('53', plain,
% 25.31/25.56      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 25.31/25.56      inference('sup-', [status(thm)], ['49', '52'])).
% 25.31/25.56  thf('54', plain, (~ (v1_xboole_0 @ sk_D)),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('55', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 25.31/25.56      inference('clc', [status(thm)], ['53', '54'])).
% 25.31/25.56  thf('56', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 25.31/25.56      inference('demod', [status(thm)], ['46', '55'])).
% 25.31/25.56  thf(t91_relat_1, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( v1_relat_1 @ B ) =>
% 25.31/25.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 25.31/25.56         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 25.31/25.56  thf('57', plain,
% 25.31/25.56      (![X22 : $i, X23 : $i]:
% 25.31/25.56         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 25.31/25.56          | ((k1_relat_1 @ (k7_relat_1 @ X23 @ X22)) = (X22))
% 25.31/25.56          | ~ (v1_relat_1 @ X23))),
% 25.31/25.56      inference('cnf', [status(esa)], [t91_relat_1])).
% 25.31/25.56  thf('58', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (~ (r1_tarski @ X0 @ sk_A)
% 25.31/25.56          | ~ (v1_relat_1 @ sk_E)
% 25.31/25.56          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['56', '57'])).
% 25.31/25.56  thf('59', plain,
% 25.31/25.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.31/25.56  thf('60', plain,
% 25.31/25.56      (![X10 : $i, X11 : $i]:
% 25.31/25.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 25.31/25.56          | (v1_relat_1 @ X10)
% 25.31/25.56          | ~ (v1_relat_1 @ X11))),
% 25.31/25.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 25.31/25.56  thf('61', plain,
% 25.31/25.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 25.31/25.56      inference('sup-', [status(thm)], ['59', '60'])).
% 25.31/25.56  thf('62', plain,
% 25.31/25.56      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 25.31/25.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 25.31/25.56  thf('63', plain, ((v1_relat_1 @ sk_E)),
% 25.31/25.56      inference('demod', [status(thm)], ['61', '62'])).
% 25.31/25.56  thf('64', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (~ (r1_tarski @ X0 @ sk_A)
% 25.31/25.56          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 25.31/25.56      inference('demod', [status(thm)], ['58', '63'])).
% 25.31/25.56  thf('65', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 25.31/25.56      inference('sup-', [status(thm)], ['39', '64'])).
% 25.31/25.56  thf('66', plain, ((v1_relat_1 @ sk_E)),
% 25.31/25.56      inference('demod', [status(thm)], ['61', '62'])).
% 25.31/25.56  thf('67', plain,
% 25.31/25.56      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 25.31/25.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 25.31/25.56      inference('demod', [status(thm)], ['27', '38', '65', '66'])).
% 25.31/25.56  thf('68', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 25.31/25.56      inference('demod', [status(thm)], ['15', '67'])).
% 25.31/25.56  thf('69', plain,
% 25.31/25.56      (![X37 : $i, X38 : $i]:
% 25.31/25.56         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.31/25.56  thf('70', plain,
% 25.31/25.56      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 25.31/25.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 25.31/25.56      inference('demod', [status(thm)], ['27', '38', '65', '66'])).
% 25.31/25.56  thf('71', plain,
% 25.31/25.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 25.31/25.56         (~ (zip_tseitin_0 @ X42 @ X43)
% 25.31/25.56          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 25.31/25.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.31/25.56  thf('72', plain,
% 25.31/25.56      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 25.31/25.56        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 25.31/25.56      inference('sup-', [status(thm)], ['70', '71'])).
% 25.31/25.56  thf('73', plain,
% 25.31/25.56      ((((sk_C) = (k1_xboole_0))
% 25.31/25.56        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 25.31/25.56      inference('sup-', [status(thm)], ['69', '72'])).
% 25.31/25.56  thf('74', plain,
% 25.31/25.56      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 25.31/25.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 25.31/25.56      inference('demod', [status(thm)], ['27', '38', '65', '66'])).
% 25.31/25.56  thf('75', plain,
% 25.31/25.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 25.31/25.56         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 25.31/25.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 25.31/25.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 25.31/25.56  thf('76', plain,
% 25.31/25.56      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 25.31/25.56         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['74', '75'])).
% 25.31/25.56  thf('77', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 25.31/25.56      inference('sup-', [status(thm)], ['39', '64'])).
% 25.31/25.56  thf('78', plain,
% 25.31/25.56      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 25.31/25.56      inference('demod', [status(thm)], ['76', '77'])).
% 25.31/25.56  thf('79', plain,
% 25.31/25.56      (![X39 : $i, X40 : $i, X41 : $i]:
% 25.31/25.56         (((X39) != (k1_relset_1 @ X39 @ X40 @ X41))
% 25.31/25.56          | (v1_funct_2 @ X41 @ X39 @ X40)
% 25.31/25.56          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.31/25.56  thf('80', plain,
% 25.31/25.56      ((((sk_B) != (sk_B))
% 25.31/25.56        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 25.31/25.56        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 25.31/25.56      inference('sup-', [status(thm)], ['78', '79'])).
% 25.31/25.56  thf('81', plain,
% 25.31/25.56      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 25.31/25.56        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 25.31/25.56      inference('simplify', [status(thm)], ['80'])).
% 25.31/25.56  thf('82', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 25.31/25.56      inference('demod', [status(thm)], ['15', '67'])).
% 25.31/25.56  thf('83', plain,
% 25.31/25.56      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 25.31/25.56      inference('clc', [status(thm)], ['81', '82'])).
% 25.31/25.56  thf('84', plain, (((sk_C) = (k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['73', '83'])).
% 25.31/25.56  thf('85', plain,
% 25.31/25.56      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 25.31/25.56      inference('demod', [status(thm)], ['68', '84'])).
% 25.31/25.56  thf('86', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 25.31/25.56      inference('sup-', [status(thm)], ['39', '64'])).
% 25.31/25.56  thf('87', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 25.31/25.56      inference('simplify', [status(thm)], ['22'])).
% 25.31/25.56  thf('88', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]:
% 25.31/25.56         (~ (v1_relat_1 @ X0)
% 25.31/25.56          | (m1_subset_1 @ X0 @ 
% 25.31/25.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 25.31/25.56          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 25.31/25.56      inference('sup-', [status(thm)], ['23', '24'])).
% 25.31/25.56  thf('89', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((m1_subset_1 @ X0 @ 
% 25.31/25.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 25.31/25.56          | ~ (v1_relat_1 @ X0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['87', '88'])).
% 25.31/25.56  thf('90', plain,
% 25.31/25.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 25.31/25.56         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 25.31/25.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 25.31/25.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 25.31/25.56  thf('91', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (~ (v1_relat_1 @ X0)
% 25.31/25.56          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 25.31/25.56              = (k1_relat_1 @ X0)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['89', '90'])).
% 25.31/25.56  thf('92', plain,
% 25.31/25.56      ((((k1_relset_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ 
% 25.31/25.56          (k7_relat_1 @ sk_E @ sk_B))
% 25.31/25.56          = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))
% 25.31/25.56        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 25.31/25.56      inference('sup+', [status(thm)], ['86', '91'])).
% 25.31/25.56  thf('93', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 25.31/25.56      inference('sup-', [status(thm)], ['39', '64'])).
% 25.31/25.56  thf('94', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['36', '37'])).
% 25.31/25.56  thf('95', plain,
% 25.31/25.56      (((k1_relset_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ 
% 25.31/25.56         (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 25.31/25.56      inference('demod', [status(thm)], ['92', '93', '94'])).
% 25.31/25.56  thf('96', plain,
% 25.31/25.56      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 25.31/25.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 25.31/25.56      inference('demod', [status(thm)], ['27', '38', '65', '66'])).
% 25.31/25.56  thf(t3_subset, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 25.31/25.56  thf('97', plain,
% 25.31/25.56      (![X7 : $i, X8 : $i]:
% 25.31/25.56         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 25.31/25.56      inference('cnf', [status(esa)], [t3_subset])).
% 25.31/25.56  thf('98', plain,
% 25.31/25.56      ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 25.31/25.56      inference('sup-', [status(thm)], ['96', '97'])).
% 25.31/25.56  thf('99', plain,
% 25.31/25.56      (![X0 : $i, X2 : $i]:
% 25.31/25.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 25.31/25.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.31/25.56  thf('100', plain,
% 25.31/25.56      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_C) @ (k7_relat_1 @ sk_E @ sk_B))
% 25.31/25.56        | ((k2_zfmisc_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_E @ sk_B)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['98', '99'])).
% 25.31/25.56  thf('101', plain, (((sk_C) = (k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['73', '83'])).
% 25.31/25.56  thf(t113_zfmisc_1, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 25.31/25.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 25.31/25.56  thf('102', plain,
% 25.31/25.56      (![X5 : $i, X6 : $i]:
% 25.31/25.56         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 25.31/25.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 25.31/25.56  thf('103', plain,
% 25.31/25.56      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 25.31/25.56      inference('simplify', [status(thm)], ['102'])).
% 25.31/25.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 25.31/25.56  thf('104', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 25.31/25.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.31/25.56  thf('105', plain, (((sk_C) = (k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['73', '83'])).
% 25.31/25.56  thf('106', plain,
% 25.31/25.56      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 25.31/25.56      inference('simplify', [status(thm)], ['102'])).
% 25.31/25.56  thf('107', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 25.31/25.56      inference('demod', [status(thm)],
% 25.31/25.56                ['100', '101', '103', '104', '105', '106'])).
% 25.31/25.56  thf('108', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 25.31/25.56      inference('demod', [status(thm)],
% 25.31/25.56                ['100', '101', '103', '104', '105', '106'])).
% 25.31/25.56  thf('109', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 25.31/25.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.31/25.56  thf('110', plain,
% 25.31/25.56      (![X7 : $i, X9 : $i]:
% 25.31/25.56         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 25.31/25.56      inference('cnf', [status(esa)], [t3_subset])).
% 25.31/25.56  thf('111', plain,
% 25.31/25.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['109', '110'])).
% 25.31/25.56  thf('112', plain,
% 25.31/25.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 25.31/25.56         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 25.31/25.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 25.31/25.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 25.31/25.56  thf('113', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]:
% 25.31/25.56         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['111', '112'])).
% 25.31/25.56  thf('114', plain,
% 25.31/25.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['109', '110'])).
% 25.31/25.56  thf(cc2_relset_1, axiom,
% 25.31/25.56    (![A:$i,B:$i,C:$i]:
% 25.31/25.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.31/25.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 25.31/25.56  thf('115', plain,
% 25.31/25.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 25.31/25.56         ((v4_relat_1 @ X24 @ X25)
% 25.31/25.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 25.31/25.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 25.31/25.56  thf('116', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 25.31/25.56      inference('sup-', [status(thm)], ['114', '115'])).
% 25.31/25.56  thf(t209_relat_1, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 25.31/25.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 25.31/25.56  thf('117', plain,
% 25.31/25.56      (![X18 : $i, X19 : $i]:
% 25.31/25.56         (((X18) = (k7_relat_1 @ X18 @ X19))
% 25.31/25.56          | ~ (v4_relat_1 @ X18 @ X19)
% 25.31/25.56          | ~ (v1_relat_1 @ X18))),
% 25.31/25.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 25.31/25.56  thf('118', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (~ (v1_relat_1 @ k1_xboole_0)
% 25.31/25.56          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['116', '117'])).
% 25.31/25.56  thf('119', plain,
% 25.31/25.56      (![X5 : $i, X6 : $i]:
% 25.31/25.56         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 25.31/25.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 25.31/25.56  thf('120', plain,
% 25.31/25.56      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 25.31/25.56      inference('simplify', [status(thm)], ['119'])).
% 25.31/25.56  thf('121', plain,
% 25.31/25.56      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 25.31/25.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 25.31/25.56  thf('122', plain, ((v1_relat_1 @ k1_xboole_0)),
% 25.31/25.56      inference('sup+', [status(thm)], ['120', '121'])).
% 25.31/25.56  thf('123', plain,
% 25.31/25.56      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 25.31/25.56      inference('demod', [status(thm)], ['118', '122'])).
% 25.31/25.56  thf(t87_relat_1, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( v1_relat_1 @ B ) =>
% 25.31/25.56       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 25.31/25.56  thf('124', plain,
% 25.31/25.56      (![X20 : $i, X21 : $i]:
% 25.31/25.56         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X21)) @ X21)
% 25.31/25.56          | ~ (v1_relat_1 @ X20))),
% 25.31/25.56      inference('cnf', [status(esa)], [t87_relat_1])).
% 25.31/25.56  thf('125', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 25.31/25.56          | ~ (v1_relat_1 @ k1_xboole_0))),
% 25.31/25.56      inference('sup+', [status(thm)], ['123', '124'])).
% 25.31/25.56  thf('126', plain, ((v1_relat_1 @ k1_xboole_0)),
% 25.31/25.56      inference('sup+', [status(thm)], ['120', '121'])).
% 25.31/25.56  thf('127', plain,
% 25.31/25.56      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 25.31/25.56      inference('demod', [status(thm)], ['125', '126'])).
% 25.31/25.56  thf('128', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 25.31/25.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.31/25.56  thf('129', plain,
% 25.31/25.56      (![X0 : $i, X2 : $i]:
% 25.31/25.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 25.31/25.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.31/25.56  thf('130', plain,
% 25.31/25.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['128', '129'])).
% 25.31/25.56  thf('131', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['127', '130'])).
% 25.31/25.56  thf('132', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]:
% 25.31/25.56         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 25.31/25.56      inference('demod', [status(thm)], ['113', '131'])).
% 25.31/25.56  thf('133', plain, (((k1_xboole_0) = (sk_B))),
% 25.31/25.56      inference('demod', [status(thm)], ['95', '107', '108', '132'])).
% 25.31/25.56  thf(dt_k7_relat_1, axiom,
% 25.31/25.56    (![A:$i,B:$i]:
% 25.31/25.56     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 25.31/25.56  thf('134', plain,
% 25.31/25.56      (![X12 : $i, X13 : $i]:
% 25.31/25.56         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 25.31/25.56      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 25.31/25.56  thf('135', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 25.31/25.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.31/25.56  thf('136', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (~ (r1_tarski @ X0 @ sk_A)
% 25.31/25.56          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 25.31/25.56      inference('demod', [status(thm)], ['58', '63'])).
% 25.31/25.56  thf('137', plain,
% 25.31/25.56      (((k1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)) = (k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['135', '136'])).
% 25.31/25.56  thf('138', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((m1_subset_1 @ X0 @ 
% 25.31/25.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 25.31/25.56          | ~ (v1_relat_1 @ X0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['87', '88'])).
% 25.31/25.56  thf('139', plain,
% 25.31/25.56      (![X7 : $i, X8 : $i]:
% 25.31/25.56         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 25.31/25.56      inference('cnf', [status(esa)], [t3_subset])).
% 25.31/25.56  thf('140', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         (~ (v1_relat_1 @ X0)
% 25.31/25.56          | (r1_tarski @ X0 @ 
% 25.31/25.56             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 25.31/25.56      inference('sup-', [status(thm)], ['138', '139'])).
% 25.31/25.56  thf('141', plain,
% 25.31/25.56      (((r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ 
% 25.31/25.56         (k2_zfmisc_1 @ k1_xboole_0 @ 
% 25.31/25.56          (k2_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0))))
% 25.31/25.56        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 25.31/25.56      inference('sup+', [status(thm)], ['137', '140'])).
% 25.31/25.56  thf('142', plain,
% 25.31/25.56      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 25.31/25.56      inference('simplify', [status(thm)], ['119'])).
% 25.31/25.56  thf('143', plain,
% 25.31/25.56      (((r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ k1_xboole_0)
% 25.31/25.56        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 25.31/25.56      inference('demod', [status(thm)], ['141', '142'])).
% 25.31/25.56  thf('144', plain,
% 25.31/25.56      ((~ (v1_relat_1 @ sk_E)
% 25.31/25.56        | (r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['134', '143'])).
% 25.31/25.56  thf('145', plain, ((v1_relat_1 @ sk_E)),
% 25.31/25.56      inference('demod', [status(thm)], ['61', '62'])).
% 25.31/25.56  thf('146', plain,
% 25.31/25.56      ((r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ k1_xboole_0)),
% 25.31/25.56      inference('demod', [status(thm)], ['144', '145'])).
% 25.31/25.56  thf('147', plain,
% 25.31/25.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 25.31/25.56      inference('sup-', [status(thm)], ['128', '129'])).
% 25.31/25.56  thf('148', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['146', '147'])).
% 25.31/25.56  thf('149', plain, (((k1_xboole_0) = (sk_B))),
% 25.31/25.56      inference('demod', [status(thm)], ['95', '107', '108', '132'])).
% 25.31/25.56  thf('150', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]:
% 25.31/25.56         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 25.31/25.56      inference('demod', [status(thm)], ['113', '131'])).
% 25.31/25.56  thf('151', plain,
% 25.31/25.56      (![X39 : $i, X40 : $i, X41 : $i]:
% 25.31/25.56         (((X39) != (k1_relset_1 @ X39 @ X40 @ X41))
% 25.31/25.56          | (v1_funct_2 @ X41 @ X39 @ X40)
% 25.31/25.56          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.31/25.56  thf('152', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]:
% 25.31/25.56         (((X1) != (k1_xboole_0))
% 25.31/25.56          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 25.31/25.56          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['150', '151'])).
% 25.31/25.56  thf('153', plain,
% 25.31/25.56      (![X0 : $i]:
% 25.31/25.56         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 25.31/25.56          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 25.31/25.56      inference('simplify', [status(thm)], ['152'])).
% 25.31/25.56  thf('154', plain,
% 25.31/25.56      (![X37 : $i, X38 : $i]:
% 25.31/25.56         ((zip_tseitin_0 @ X37 @ X38) | ((X38) != (k1_xboole_0)))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.31/25.56  thf('155', plain, (![X37 : $i]: (zip_tseitin_0 @ X37 @ k1_xboole_0)),
% 25.31/25.56      inference('simplify', [status(thm)], ['154'])).
% 25.31/25.56  thf('156', plain,
% 25.31/25.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.31/25.56      inference('sup-', [status(thm)], ['109', '110'])).
% 25.31/25.56  thf('157', plain,
% 25.31/25.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 25.31/25.56         (~ (zip_tseitin_0 @ X42 @ X43)
% 25.31/25.56          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 25.31/25.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 25.31/25.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.31/25.56  thf('158', plain,
% 25.31/25.56      (![X0 : $i, X1 : $i]:
% 25.31/25.56         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 25.31/25.56      inference('sup-', [status(thm)], ['156', '157'])).
% 25.31/25.56  thf('159', plain,
% 25.31/25.56      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 25.31/25.56      inference('sup-', [status(thm)], ['155', '158'])).
% 25.31/25.56  thf('160', plain,
% 25.31/25.56      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 25.31/25.56      inference('demod', [status(thm)], ['153', '159'])).
% 25.31/25.56  thf('161', plain, ($false),
% 25.31/25.56      inference('demod', [status(thm)], ['85', '133', '148', '149', '160'])).
% 25.31/25.56  
% 25.31/25.56  % SZS output end Refutation
% 25.31/25.56  
% 25.31/25.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
