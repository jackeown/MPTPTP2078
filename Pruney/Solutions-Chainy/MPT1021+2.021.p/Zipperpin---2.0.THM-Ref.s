%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hl6LkAVZPS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:13 EST 2020

% Result     : Theorem 6.46s
% Output     : Refutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 452 expanded)
%              Number of leaves         :   46 ( 158 expanded)
%              Depth                    :   16
%              Number of atoms          : 1495 (9649 expanded)
%              Number of equality atoms :   65 ( 102 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_funct_2 @ X50 @ X49 )
        = ( k2_funct_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X50 ) ) )
      | ~ ( v3_funct_2 @ X49 @ X50 @ X50 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('37',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('41',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('45',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','52'])).

thf('54',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('55',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','52'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('61',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('67',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','64','65','66'])).

thf('68',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','52'])).

thf('74',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('75',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('76',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('81',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','77','78','79','80'])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('84',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','82','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('86',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('95',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('96',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','97'])).

thf('99',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','98'])).

thf('100',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
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

thf('101',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('102',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('104',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('108',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('109',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('111',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('112',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['110','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['113'])).

thf('115',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['109','114'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['106','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('118',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('119',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['99','116','117','118','119','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hl6LkAVZPS
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:09:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 6.46/6.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.46/6.74  % Solved by: fo/fo7.sh
% 6.46/6.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.46/6.74  % done 4275 iterations in 6.257s
% 6.46/6.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.46/6.74  % SZS output start Refutation
% 6.46/6.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.46/6.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.46/6.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.46/6.74  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.46/6.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.46/6.74  thf(sk_B_type, type, sk_B: $i).
% 6.46/6.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.46/6.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.46/6.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.46/6.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.46/6.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.46/6.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.46/6.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.46/6.74  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 6.46/6.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.46/6.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.46/6.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.46/6.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.46/6.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.46/6.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.46/6.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.46/6.74  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.46/6.74  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 6.46/6.74  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 6.46/6.74  thf(sk_A_type, type, sk_A: $i).
% 6.46/6.74  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 6.46/6.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.46/6.74  thf(t61_funct_1, axiom,
% 6.46/6.74    (![A:$i]:
% 6.46/6.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.46/6.74       ( ( v2_funct_1 @ A ) =>
% 6.46/6.74         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 6.46/6.74             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 6.46/6.74           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 6.46/6.74             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.46/6.74  thf('0', plain,
% 6.46/6.74      (![X11 : $i]:
% 6.46/6.74         (~ (v2_funct_1 @ X11)
% 6.46/6.74          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 6.46/6.74              = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 6.46/6.74          | ~ (v1_funct_1 @ X11)
% 6.46/6.74          | ~ (v1_relat_1 @ X11))),
% 6.46/6.74      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.46/6.74  thf(redefinition_k6_partfun1, axiom,
% 6.46/6.74    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.46/6.74  thf('1', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.46/6.74  thf('2', plain,
% 6.46/6.74      (![X11 : $i]:
% 6.46/6.74         (~ (v2_funct_1 @ X11)
% 6.46/6.74          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 6.46/6.74              = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 6.46/6.74          | ~ (v1_funct_1 @ X11)
% 6.46/6.74          | ~ (v1_relat_1 @ X11))),
% 6.46/6.74      inference('demod', [status(thm)], ['0', '1'])).
% 6.46/6.74  thf(t88_funct_2, conjecture,
% 6.46/6.74    (![A:$i,B:$i]:
% 6.46/6.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.46/6.74         ( v3_funct_2 @ B @ A @ A ) & 
% 6.46/6.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.46/6.74       ( ( r2_relset_1 @
% 6.46/6.74           A @ A @ 
% 6.46/6.74           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 6.46/6.74           ( k6_partfun1 @ A ) ) & 
% 6.46/6.74         ( r2_relset_1 @
% 6.46/6.74           A @ A @ 
% 6.46/6.74           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 6.46/6.74           ( k6_partfun1 @ A ) ) ) ))).
% 6.46/6.74  thf(zf_stmt_0, negated_conjecture,
% 6.46/6.74    (~( ![A:$i,B:$i]:
% 6.46/6.74        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.46/6.74            ( v3_funct_2 @ B @ A @ A ) & 
% 6.46/6.74            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.46/6.74          ( ( r2_relset_1 @
% 6.46/6.74              A @ A @ 
% 6.46/6.74              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 6.46/6.74              ( k6_partfun1 @ A ) ) & 
% 6.46/6.74            ( r2_relset_1 @
% 6.46/6.74              A @ A @ 
% 6.46/6.74              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 6.46/6.74              ( k6_partfun1 @ A ) ) ) ) )),
% 6.46/6.74    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 6.46/6.74  thf('3', plain,
% 6.46/6.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.46/6.74           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 6.46/6.74            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 6.46/6.74           (k6_partfun1 @ sk_A))
% 6.46/6.74        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.46/6.74             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 6.46/6.74              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 6.46/6.74             (k6_partfun1 @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('4', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(redefinition_k2_funct_2, axiom,
% 6.46/6.74    (![A:$i,B:$i]:
% 6.46/6.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.46/6.74         ( v3_funct_2 @ B @ A @ A ) & 
% 6.46/6.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.46/6.74       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 6.46/6.74  thf('5', plain,
% 6.46/6.74      (![X49 : $i, X50 : $i]:
% 6.46/6.74         (((k2_funct_2 @ X50 @ X49) = (k2_funct_1 @ X49))
% 6.46/6.74          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X50)))
% 6.46/6.74          | ~ (v3_funct_2 @ X49 @ X50 @ X50)
% 6.46/6.74          | ~ (v1_funct_2 @ X49 @ X50 @ X50)
% 6.46/6.74          | ~ (v1_funct_1 @ X49))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 6.46/6.74  thf('6', plain,
% 6.46/6.74      ((~ (v1_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['4', '5'])).
% 6.46/6.74  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 6.46/6.74  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 6.46/6.74  thf('12', plain,
% 6.46/6.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.46/6.74           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 6.46/6.74            (k2_funct_1 @ sk_B)) @ 
% 6.46/6.74           (k6_partfun1 @ sk_A))
% 6.46/6.74        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.46/6.74             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 6.46/6.74              sk_B) @ 
% 6.46/6.74             (k6_partfun1 @ sk_A)))),
% 6.46/6.74      inference('demod', [status(thm)], ['3', '10', '11'])).
% 6.46/6.74  thf('13', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('14', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(dt_k2_funct_2, axiom,
% 6.46/6.74    (![A:$i,B:$i]:
% 6.46/6.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.46/6.74         ( v3_funct_2 @ B @ A @ A ) & 
% 6.46/6.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.46/6.74       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 6.46/6.74         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 6.46/6.74         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 6.46/6.74         ( m1_subset_1 @
% 6.46/6.74           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 6.46/6.74  thf('15', plain,
% 6.46/6.74      (![X39 : $i, X40 : $i]:
% 6.46/6.74         ((m1_subset_1 @ (k2_funct_2 @ X39 @ X40) @ 
% 6.46/6.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 6.46/6.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 6.46/6.74          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 6.46/6.74          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 6.46/6.74          | ~ (v1_funct_1 @ X40))),
% 6.46/6.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 6.46/6.74  thf('16', plain,
% 6.46/6.74      ((~ (v1_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 6.46/6.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.46/6.74      inference('sup-', [status(thm)], ['14', '15'])).
% 6.46/6.74  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('20', plain,
% 6.46/6.74      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 6.46/6.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 6.46/6.74  thf(redefinition_k1_partfun1, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.46/6.74     ( ( ( v1_funct_1 @ E ) & 
% 6.46/6.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.46/6.74         ( v1_funct_1 @ F ) & 
% 6.46/6.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.46/6.74       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.46/6.74  thf('21', plain,
% 6.46/6.74      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 6.46/6.74         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 6.46/6.74          | ~ (v1_funct_1 @ X43)
% 6.46/6.74          | ~ (v1_funct_1 @ X46)
% 6.46/6.74          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 6.46/6.74          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 6.46/6.74              = (k5_relat_1 @ X43 @ X46)))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.46/6.74  thf('22', plain,
% 6.46/6.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.74         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 6.46/6.74            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 6.46/6.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.46/6.74          | ~ (v1_funct_1 @ X0)
% 6.46/6.74          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['20', '21'])).
% 6.46/6.74  thf('23', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('24', plain,
% 6.46/6.74      (![X39 : $i, X40 : $i]:
% 6.46/6.74         ((v1_funct_1 @ (k2_funct_2 @ X39 @ X40))
% 6.46/6.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 6.46/6.74          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 6.46/6.74          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 6.46/6.74          | ~ (v1_funct_1 @ X40))),
% 6.46/6.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 6.46/6.74  thf('25', plain,
% 6.46/6.74      ((~ (v1_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['23', '24'])).
% 6.46/6.74  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 6.46/6.74  thf('30', plain,
% 6.46/6.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.74         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 6.46/6.74            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 6.46/6.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.46/6.74          | ~ (v1_funct_1 @ X0))),
% 6.46/6.74      inference('demod', [status(thm)], ['22', '29'])).
% 6.46/6.74  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 6.46/6.74  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 6.46/6.74  thf('33', plain,
% 6.46/6.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.74         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 6.46/6.74            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 6.46/6.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.46/6.74          | ~ (v1_funct_1 @ X0))),
% 6.46/6.74      inference('demod', [status(thm)], ['30', '31', '32'])).
% 6.46/6.74  thf('34', plain,
% 6.46/6.74      ((~ (v1_funct_1 @ sk_B)
% 6.46/6.74        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 6.46/6.74            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['13', '33'])).
% 6.46/6.74  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('36', plain,
% 6.46/6.74      (![X11 : $i]:
% 6.46/6.74         (~ (v2_funct_1 @ X11)
% 6.46/6.74          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 6.46/6.74              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 6.46/6.74          | ~ (v1_funct_1 @ X11)
% 6.46/6.74          | ~ (v1_relat_1 @ X11))),
% 6.46/6.74      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.46/6.74  thf('37', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.46/6.74  thf('38', plain,
% 6.46/6.74      (![X11 : $i]:
% 6.46/6.74         (~ (v2_funct_1 @ X11)
% 6.46/6.74          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 6.46/6.74              = (k6_partfun1 @ (k2_relat_1 @ X11)))
% 6.46/6.74          | ~ (v1_funct_1 @ X11)
% 6.46/6.74          | ~ (v1_relat_1 @ X11))),
% 6.46/6.74      inference('demod', [status(thm)], ['36', '37'])).
% 6.46/6.74  thf('39', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(cc2_funct_2, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i]:
% 6.46/6.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.74       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 6.46/6.74         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 6.46/6.74  thf('40', plain,
% 6.46/6.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.46/6.74         (~ (v1_funct_1 @ X26)
% 6.46/6.74          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 6.46/6.74          | (v2_funct_2 @ X26 @ X28)
% 6.46/6.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 6.46/6.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 6.46/6.74  thf('41', plain,
% 6.46/6.74      (((v2_funct_2 @ sk_B @ sk_A)
% 6.46/6.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | ~ (v1_funct_1 @ sk_B))),
% 6.46/6.74      inference('sup-', [status(thm)], ['39', '40'])).
% 6.46/6.74  thf('42', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('44', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 6.46/6.74      inference('demod', [status(thm)], ['41', '42', '43'])).
% 6.46/6.74  thf(d3_funct_2, axiom,
% 6.46/6.74    (![A:$i,B:$i]:
% 6.46/6.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 6.46/6.74       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 6.46/6.74  thf('45', plain,
% 6.46/6.74      (![X37 : $i, X38 : $i]:
% 6.46/6.74         (~ (v2_funct_2 @ X38 @ X37)
% 6.46/6.74          | ((k2_relat_1 @ X38) = (X37))
% 6.46/6.74          | ~ (v5_relat_1 @ X38 @ X37)
% 6.46/6.74          | ~ (v1_relat_1 @ X38))),
% 6.46/6.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 6.46/6.74  thf('46', plain,
% 6.46/6.74      ((~ (v1_relat_1 @ sk_B)
% 6.46/6.74        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 6.46/6.74        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['44', '45'])).
% 6.46/6.74  thf('47', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(cc1_relset_1, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i]:
% 6.46/6.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.74       ( v1_relat_1 @ C ) ))).
% 6.46/6.74  thf('48', plain,
% 6.46/6.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.46/6.74         ((v1_relat_1 @ X13)
% 6.46/6.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 6.46/6.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.46/6.74  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 6.46/6.74      inference('sup-', [status(thm)], ['47', '48'])).
% 6.46/6.74  thf('50', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(cc2_relset_1, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i]:
% 6.46/6.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.46/6.74  thf('51', plain,
% 6.46/6.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.46/6.74         ((v5_relat_1 @ X16 @ X18)
% 6.46/6.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 6.46/6.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.46/6.74  thf('52', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 6.46/6.74      inference('sup-', [status(thm)], ['50', '51'])).
% 6.46/6.74  thf('53', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 6.46/6.74      inference('demod', [status(thm)], ['46', '49', '52'])).
% 6.46/6.74  thf('54', plain,
% 6.46/6.74      (![X11 : $i]:
% 6.46/6.74         (~ (v2_funct_1 @ X11)
% 6.46/6.74          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 6.46/6.74              = (k6_partfun1 @ (k2_relat_1 @ X11)))
% 6.46/6.74          | ~ (v1_funct_1 @ X11)
% 6.46/6.74          | ~ (v1_relat_1 @ X11))),
% 6.46/6.74      inference('demod', [status(thm)], ['36', '37'])).
% 6.46/6.74  thf(dt_k6_partfun1, axiom,
% 6.46/6.74    (![A:$i]:
% 6.46/6.74     ( ( m1_subset_1 @
% 6.46/6.74         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 6.46/6.74       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 6.46/6.74  thf('55', plain,
% 6.46/6.74      (![X42 : $i]:
% 6.46/6.74         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 6.46/6.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 6.46/6.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.46/6.74  thf('56', plain,
% 6.46/6.74      (![X0 : $i]:
% 6.46/6.74         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 6.46/6.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 6.46/6.74          | ~ (v1_relat_1 @ X0)
% 6.46/6.74          | ~ (v1_funct_1 @ X0)
% 6.46/6.74          | ~ (v2_funct_1 @ X0))),
% 6.46/6.74      inference('sup+', [status(thm)], ['54', '55'])).
% 6.46/6.74  thf('57', plain,
% 6.46/6.74      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 6.46/6.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 6.46/6.74        | ~ (v2_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v1_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v1_relat_1 @ sk_B))),
% 6.46/6.74      inference('sup+', [status(thm)], ['53', '56'])).
% 6.46/6.74  thf('58', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 6.46/6.74      inference('demod', [status(thm)], ['46', '49', '52'])).
% 6.46/6.74  thf('59', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('60', plain,
% 6.46/6.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.46/6.74         (~ (v1_funct_1 @ X26)
% 6.46/6.74          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 6.46/6.74          | (v2_funct_1 @ X26)
% 6.46/6.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 6.46/6.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 6.46/6.74  thf('61', plain,
% 6.46/6.74      (((v2_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | ~ (v1_funct_1 @ sk_B))),
% 6.46/6.74      inference('sup-', [status(thm)], ['59', '60'])).
% 6.46/6.74  thf('62', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('64', plain, ((v2_funct_1 @ sk_B)),
% 6.46/6.74      inference('demod', [status(thm)], ['61', '62', '63'])).
% 6.46/6.74  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 6.46/6.74      inference('sup-', [status(thm)], ['47', '48'])).
% 6.46/6.74  thf('67', plain,
% 6.46/6.74      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 6.46/6.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('demod', [status(thm)], ['57', '58', '64', '65', '66'])).
% 6.46/6.74  thf('68', plain,
% 6.46/6.74      (![X42 : $i]:
% 6.46/6.74         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 6.46/6.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 6.46/6.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.46/6.74  thf(redefinition_r2_relset_1, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i,D:$i]:
% 6.46/6.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.46/6.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.46/6.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.46/6.74  thf('69', plain,
% 6.46/6.74      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 6.46/6.74         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.46/6.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.46/6.74          | ((X22) = (X25))
% 6.46/6.74          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.46/6.74  thf('70', plain,
% 6.46/6.74      (![X0 : $i, X1 : $i]:
% 6.46/6.74         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 6.46/6.74          | ((k6_partfun1 @ X0) = (X1))
% 6.46/6.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 6.46/6.74      inference('sup-', [status(thm)], ['68', '69'])).
% 6.46/6.74  thf('71', plain,
% 6.46/6.74      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 6.46/6.74        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 6.46/6.74             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['67', '70'])).
% 6.46/6.74  thf('72', plain,
% 6.46/6.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 6.46/6.74           (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 6.46/6.74        | ~ (v1_relat_1 @ sk_B)
% 6.46/6.74        | ~ (v1_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v2_funct_1 @ sk_B)
% 6.46/6.74        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['38', '71'])).
% 6.46/6.74  thf('73', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 6.46/6.74      inference('demod', [status(thm)], ['46', '49', '52'])).
% 6.46/6.74  thf('74', plain,
% 6.46/6.74      (![X42 : $i]:
% 6.46/6.74         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 6.46/6.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 6.46/6.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.46/6.74  thf('75', plain,
% 6.46/6.74      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 6.46/6.74         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.46/6.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.46/6.74          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 6.46/6.74          | ((X22) != (X25)))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.46/6.74  thf('76', plain,
% 6.46/6.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.46/6.74         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 6.46/6.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.46/6.74      inference('simplify', [status(thm)], ['75'])).
% 6.46/6.74  thf('77', plain,
% 6.46/6.74      (![X0 : $i]:
% 6.46/6.74         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 6.46/6.74      inference('sup-', [status(thm)], ['74', '76'])).
% 6.46/6.74  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 6.46/6.74      inference('sup-', [status(thm)], ['47', '48'])).
% 6.46/6.74  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('80', plain, ((v2_funct_1 @ sk_B)),
% 6.46/6.74      inference('demod', [status(thm)], ['61', '62', '63'])).
% 6.46/6.74  thf('81', plain,
% 6.46/6.74      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['72', '73', '77', '78', '79', '80'])).
% 6.46/6.74  thf('82', plain,
% 6.46/6.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 6.46/6.74         = (k6_partfun1 @ sk_A))),
% 6.46/6.74      inference('demod', [status(thm)], ['34', '35', '81'])).
% 6.46/6.74  thf('83', plain,
% 6.46/6.74      (![X0 : $i]:
% 6.46/6.74         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 6.46/6.74      inference('sup-', [status(thm)], ['74', '76'])).
% 6.46/6.74  thf('84', plain,
% 6.46/6.74      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.46/6.74          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 6.46/6.74          (k6_partfun1 @ sk_A))),
% 6.46/6.74      inference('demod', [status(thm)], ['12', '82', '83'])).
% 6.46/6.74  thf('85', plain,
% 6.46/6.74      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 6.46/6.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 6.46/6.74  thf('86', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 6.46/6.74  thf('87', plain,
% 6.46/6.74      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.46/6.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('demod', [status(thm)], ['85', '86'])).
% 6.46/6.74  thf('88', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('89', plain,
% 6.46/6.74      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 6.46/6.74         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 6.46/6.74          | ~ (v1_funct_1 @ X43)
% 6.46/6.74          | ~ (v1_funct_1 @ X46)
% 6.46/6.74          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 6.46/6.74          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 6.46/6.74              = (k5_relat_1 @ X43 @ X46)))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.46/6.74  thf('90', plain,
% 6.46/6.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.74         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 6.46/6.74            = (k5_relat_1 @ sk_B @ X0))
% 6.46/6.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.46/6.74          | ~ (v1_funct_1 @ X0)
% 6.46/6.74          | ~ (v1_funct_1 @ sk_B))),
% 6.46/6.74      inference('sup-', [status(thm)], ['88', '89'])).
% 6.46/6.74  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('92', plain,
% 6.46/6.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.74         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 6.46/6.74            = (k5_relat_1 @ sk_B @ X0))
% 6.46/6.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.46/6.74          | ~ (v1_funct_1 @ X0))),
% 6.46/6.74      inference('demod', [status(thm)], ['90', '91'])).
% 6.46/6.74  thf('93', plain,
% 6.46/6.74      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.46/6.74        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 6.46/6.74            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 6.46/6.74      inference('sup-', [status(thm)], ['87', '92'])).
% 6.46/6.74  thf('94', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 6.46/6.74  thf('95', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 6.46/6.74  thf('96', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['94', '95'])).
% 6.46/6.74  thf('97', plain,
% 6.46/6.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 6.46/6.74         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 6.46/6.74      inference('demod', [status(thm)], ['93', '96'])).
% 6.46/6.74  thf('98', plain,
% 6.46/6.74      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.46/6.74          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_partfun1 @ sk_A))),
% 6.46/6.74      inference('demod', [status(thm)], ['84', '97'])).
% 6.46/6.74  thf('99', plain,
% 6.46/6.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ (k1_relat_1 @ sk_B)) @ 
% 6.46/6.74           (k6_partfun1 @ sk_A))
% 6.46/6.74        | ~ (v1_relat_1 @ sk_B)
% 6.46/6.74        | ~ (v1_funct_1 @ sk_B)
% 6.46/6.74        | ~ (v2_funct_1 @ sk_B))),
% 6.46/6.74      inference('sup-', [status(thm)], ['2', '98'])).
% 6.46/6.74  thf('100', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(d1_funct_2, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i]:
% 6.46/6.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.46/6.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.46/6.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.46/6.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.46/6.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.46/6.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.46/6.74  thf(zf_stmt_1, axiom,
% 6.46/6.74    (![C:$i,B:$i,A:$i]:
% 6.46/6.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.46/6.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.46/6.74  thf('101', plain,
% 6.46/6.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 6.46/6.74         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 6.46/6.74          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 6.46/6.74          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.46/6.74  thf('102', plain,
% 6.46/6.74      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 6.46/6.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 6.46/6.74      inference('sup-', [status(thm)], ['100', '101'])).
% 6.46/6.74  thf('103', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(redefinition_k1_relset_1, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i]:
% 6.46/6.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.46/6.74  thf('104', plain,
% 6.46/6.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.46/6.74         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 6.46/6.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 6.46/6.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.46/6.74  thf('105', plain,
% 6.46/6.74      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 6.46/6.74      inference('sup-', [status(thm)], ['103', '104'])).
% 6.46/6.74  thf('106', plain,
% 6.46/6.74      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_B)))),
% 6.46/6.74      inference('demod', [status(thm)], ['102', '105'])).
% 6.46/6.74  thf('107', plain,
% 6.46/6.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.46/6.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.46/6.74  thf(zf_stmt_4, axiom,
% 6.46/6.74    (![B:$i,A:$i]:
% 6.46/6.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.46/6.74       ( zip_tseitin_0 @ B @ A ) ))).
% 6.46/6.74  thf(zf_stmt_5, axiom,
% 6.46/6.74    (![A:$i,B:$i,C:$i]:
% 6.46/6.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.46/6.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.46/6.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.46/6.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.46/6.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.46/6.74  thf('108', plain,
% 6.46/6.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.46/6.74         (~ (zip_tseitin_0 @ X34 @ X35)
% 6.46/6.74          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 6.46/6.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.46/6.74  thf('109', plain,
% 6.46/6.74      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 6.46/6.74      inference('sup-', [status(thm)], ['107', '108'])).
% 6.46/6.74  thf('110', plain,
% 6.46/6.74      (![X29 : $i, X30 : $i]:
% 6.46/6.74         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.46/6.74  thf('111', plain,
% 6.46/6.74      (![X29 : $i, X30 : $i]:
% 6.46/6.74         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.46/6.74  thf('112', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 6.46/6.74      inference('simplify', [status(thm)], ['111'])).
% 6.46/6.74  thf('113', plain,
% 6.46/6.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.46/6.74         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 6.46/6.74      inference('sup+', [status(thm)], ['110', '112'])).
% 6.46/6.74  thf('114', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 6.46/6.74      inference('eq_fact', [status(thm)], ['113'])).
% 6.46/6.74  thf('115', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 6.46/6.74      inference('demod', [status(thm)], ['109', '114'])).
% 6.46/6.74  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 6.46/6.74      inference('demod', [status(thm)], ['106', '115'])).
% 6.46/6.74  thf('117', plain,
% 6.46/6.74      (![X0 : $i]:
% 6.46/6.74         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 6.46/6.74      inference('sup-', [status(thm)], ['74', '76'])).
% 6.46/6.74  thf('118', plain, ((v1_relat_1 @ sk_B)),
% 6.46/6.74      inference('sup-', [status(thm)], ['47', '48'])).
% 6.46/6.74  thf('119', plain, ((v1_funct_1 @ sk_B)),
% 6.46/6.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.46/6.74  thf('120', plain, ((v2_funct_1 @ sk_B)),
% 6.46/6.74      inference('demod', [status(thm)], ['61', '62', '63'])).
% 6.46/6.74  thf('121', plain, ($false),
% 6.46/6.74      inference('demod', [status(thm)],
% 6.46/6.74                ['99', '116', '117', '118', '119', '120'])).
% 6.46/6.74  
% 6.46/6.74  % SZS output end Refutation
% 6.46/6.74  
% 6.59/6.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
