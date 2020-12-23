%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UvsCxzngei

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:16 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 480 expanded)
%              Number of leaves         :   37 ( 160 expanded)
%              Depth                    :   12
%              Number of atoms          : 1523 (10773 expanded)
%              Number of equality atoms :   47 (  92 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('33',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('49',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('51',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('52',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['47','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('63',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','66','67','70'])).

thf('72',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','71'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('78',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('89',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('90',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('93',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('97',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('100',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('101',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('102',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['98','99','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('105',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['98','99','102'])).

thf('109',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('110',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('112',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('114',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['90','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['98','99','102'])).

thf('117',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('118',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('120',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['75','87','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UvsCxzngei
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.15/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.35  % Solved by: fo/fo7.sh
% 1.15/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.35  % done 1133 iterations in 0.888s
% 1.15/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.35  % SZS output start Refutation
% 1.15/1.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.35  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.15/1.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.35  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.15/1.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.35  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.15/1.35  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.15/1.35  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.15/1.35  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.15/1.35  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.15/1.35  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.15/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.35  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.15/1.35  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.15/1.35  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.15/1.35  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.15/1.35  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.15/1.35  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.15/1.35  thf(t88_funct_2, conjecture,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.35         ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.35         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.35       ( ( r2_relset_1 @
% 1.15/1.35           A @ A @ 
% 1.15/1.35           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.15/1.35           ( k6_partfun1 @ A ) ) & 
% 1.15/1.35         ( r2_relset_1 @
% 1.15/1.35           A @ A @ 
% 1.15/1.35           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.15/1.35           ( k6_partfun1 @ A ) ) ) ))).
% 1.15/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.35    (~( ![A:$i,B:$i]:
% 1.15/1.35        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.35            ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.35            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.35          ( ( r2_relset_1 @
% 1.15/1.35              A @ A @ 
% 1.15/1.35              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.15/1.35              ( k6_partfun1 @ A ) ) & 
% 1.15/1.35            ( r2_relset_1 @
% 1.15/1.35              A @ A @ 
% 1.15/1.35              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.15/1.35              ( k6_partfun1 @ A ) ) ) ) )),
% 1.15/1.35    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.15/1.35  thf('0', plain,
% 1.15/1.35      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.15/1.35           (k6_partfun1 @ sk_A))
% 1.15/1.35        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.35              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35             (k6_partfun1 @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('1', plain,
% 1.15/1.35      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.35            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35           (k6_partfun1 @ sk_A)))
% 1.15/1.35         <= (~
% 1.15/1.35             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.35                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35               (k6_partfun1 @ sk_A))))),
% 1.15/1.35      inference('split', [status(esa)], ['0'])).
% 1.15/1.35  thf('2', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(redefinition_k2_funct_2, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.35         ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.35         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.35       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.15/1.35  thf('3', plain,
% 1.15/1.35      (![X29 : $i, X30 : $i]:
% 1.15/1.35         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 1.15/1.35          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 1.15/1.35          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 1.15/1.35          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 1.15/1.35          | ~ (v1_funct_1 @ X29))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.15/1.35  thf('4', plain,
% 1.15/1.35      ((~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('6', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('7', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.35  thf('9', plain,
% 1.15/1.35      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.15/1.35            sk_B_1) @ 
% 1.15/1.35           (k6_partfun1 @ sk_A)))
% 1.15/1.35         <= (~
% 1.15/1.35             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.35                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35               (k6_partfun1 @ sk_A))))),
% 1.15/1.35      inference('demod', [status(thm)], ['1', '8'])).
% 1.15/1.35  thf('10', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(dt_k2_funct_2, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.35         ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.35         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.35       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.15/1.35         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.15/1.35         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.15/1.35         ( m1_subset_1 @
% 1.15/1.35           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.15/1.35  thf('11', plain,
% 1.15/1.35      (![X21 : $i, X22 : $i]:
% 1.15/1.35         ((m1_subset_1 @ (k2_funct_2 @ X21 @ X22) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 1.15/1.35          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 1.15/1.35          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.35          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.35          | ~ (v1_funct_1 @ X22))),
% 1.15/1.35      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.15/1.35  thf('12', plain,
% 1.15/1.35      ((~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['10', '11'])).
% 1.15/1.35  thf('13', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('14', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('15', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('16', plain,
% 1.15/1.35      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 1.15/1.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 1.15/1.35  thf('17', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.35  thf('18', plain,
% 1.15/1.35      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 1.15/1.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('demod', [status(thm)], ['16', '17'])).
% 1.15/1.35  thf('19', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(redefinition_k1_partfun1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.15/1.35     ( ( ( v1_funct_1 @ E ) & 
% 1.15/1.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.35         ( v1_funct_1 @ F ) & 
% 1.15/1.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.15/1.35       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.15/1.35  thf('20', plain,
% 1.15/1.35      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.35         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.15/1.35          | ~ (v1_funct_1 @ X23)
% 1.15/1.35          | ~ (v1_funct_1 @ X26)
% 1.15/1.35          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.15/1.35          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 1.15/1.35              = (k5_relat_1 @ X23 @ X26)))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.15/1.35  thf('21', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 1.15/1.35            = (k5_relat_1 @ sk_B_1 @ X0))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X0)
% 1.15/1.35          | ~ (v1_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['19', '20'])).
% 1.15/1.35  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('23', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 1.15/1.35            = (k5_relat_1 @ sk_B_1 @ X0))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X0))),
% 1.15/1.35      inference('demod', [status(thm)], ['21', '22'])).
% 1.15/1.35  thf('24', plain,
% 1.15/1.35      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 1.15/1.35        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35            (k2_funct_1 @ sk_B_1))
% 1.15/1.35            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['18', '23'])).
% 1.15/1.35  thf('25', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('26', plain,
% 1.15/1.35      (![X21 : $i, X22 : $i]:
% 1.15/1.35         ((v1_funct_1 @ (k2_funct_2 @ X21 @ X22))
% 1.15/1.35          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 1.15/1.35          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.35          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.35          | ~ (v1_funct_1 @ X22))),
% 1.15/1.35      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.15/1.35  thf('27', plain,
% 1.15/1.35      ((~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['25', '26'])).
% 1.15/1.35  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('29', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('30', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('31', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 1.15/1.35  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.35  thf('33', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['31', '32'])).
% 1.15/1.35  thf('34', plain,
% 1.15/1.35      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35         (k2_funct_1 @ sk_B_1)) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 1.15/1.35      inference('demod', [status(thm)], ['24', '33'])).
% 1.15/1.35  thf('35', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.35  thf('36', plain,
% 1.15/1.35      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.15/1.35           (k6_partfun1 @ sk_A)))
% 1.15/1.35         <= (~
% 1.15/1.35             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.15/1.35               (k6_partfun1 @ sk_A))))),
% 1.15/1.35      inference('split', [status(esa)], ['0'])).
% 1.15/1.35  thf('37', plain,
% 1.15/1.35      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35            (k2_funct_1 @ sk_B_1)) @ 
% 1.15/1.35           (k6_partfun1 @ sk_A)))
% 1.15/1.35         <= (~
% 1.15/1.35             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.15/1.35               (k6_partfun1 @ sk_A))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['35', '36'])).
% 1.15/1.35  thf('38', plain,
% 1.15/1.35      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35           (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ (k6_partfun1 @ sk_A)))
% 1.15/1.35         <= (~
% 1.15/1.35             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.15/1.35               (k6_partfun1 @ sk_A))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['34', '37'])).
% 1.15/1.35  thf('39', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(t67_funct_2, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.35         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.35       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.15/1.35  thf('40', plain,
% 1.15/1.35      (![X32 : $i, X33 : $i]:
% 1.15/1.35         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 1.15/1.35          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 1.15/1.35          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 1.15/1.35          | ~ (v1_funct_1 @ X33))),
% 1.15/1.35      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.15/1.35  thf('41', plain,
% 1.15/1.35      ((~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['39', '40'])).
% 1.15/1.35  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('43', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('44', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(redefinition_k1_relset_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.35       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.15/1.35  thf('45', plain,
% 1.15/1.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.15/1.35         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.15/1.35          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.15/1.35  thf('46', plain,
% 1.15/1.35      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['44', '45'])).
% 1.15/1.35  thf('47', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.15/1.35  thf(t61_funct_1, axiom,
% 1.15/1.35    (![A:$i]:
% 1.15/1.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.35       ( ( v2_funct_1 @ A ) =>
% 1.15/1.35         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.15/1.35             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.15/1.35           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.15/1.35             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.35  thf('48', plain,
% 1.15/1.35      (![X1 : $i]:
% 1.15/1.35         (~ (v2_funct_1 @ X1)
% 1.15/1.35          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 1.15/1.35              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X1)
% 1.15/1.35          | ~ (v1_relat_1 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.15/1.35  thf(redefinition_k6_partfun1, axiom,
% 1.15/1.35    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.15/1.35  thf('49', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.35  thf('50', plain,
% 1.15/1.35      (![X1 : $i]:
% 1.15/1.35         (~ (v2_funct_1 @ X1)
% 1.15/1.35          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 1.15/1.35              = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X1)
% 1.15/1.35          | ~ (v1_relat_1 @ X1))),
% 1.15/1.35      inference('demod', [status(thm)], ['48', '49'])).
% 1.15/1.35  thf(t29_relset_1, axiom,
% 1.15/1.35    (![A:$i]:
% 1.15/1.35     ( m1_subset_1 @
% 1.15/1.35       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.15/1.35  thf('51', plain,
% 1.15/1.35      (![X15 : $i]:
% 1.15/1.35         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 1.15/1.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.15/1.35  thf('52', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.35  thf('53', plain,
% 1.15/1.35      (![X15 : $i]:
% 1.15/1.35         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.15/1.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.35      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.35  thf(reflexivity_r2_relset_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.35       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 1.15/1.35  thf('54', plain,
% 1.15/1.35      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.15/1.35         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 1.15/1.35          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.15/1.35          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.15/1.35      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 1.15/1.35  thf('55', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.15/1.35      inference('condensation', [status(thm)], ['54'])).
% 1.15/1.35  thf('56', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['53', '55'])).
% 1.15/1.35  thf('57', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((r2_relset_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.15/1.35           (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 1.15/1.35           (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.15/1.35          | ~ (v1_relat_1 @ X0)
% 1.15/1.35          | ~ (v1_funct_1 @ X0)
% 1.15/1.35          | ~ (v2_funct_1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['50', '56'])).
% 1.15/1.35  thf('58', plain,
% 1.15/1.35      (((r2_relset_1 @ sk_A @ (k1_relat_1 @ sk_B_1) @ 
% 1.15/1.35         (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 1.15/1.35         (k6_partfun1 @ (k1_relat_1 @ sk_B_1)))
% 1.15/1.35        | ~ (v2_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_relat_1 @ sk_B_1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['47', '57'])).
% 1.15/1.35  thf('59', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.15/1.35  thf('60', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.15/1.35  thf('61', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(cc2_funct_2, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.35       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.15/1.35         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.15/1.35  thf('62', plain,
% 1.15/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.15/1.35         (~ (v1_funct_1 @ X16)
% 1.15/1.35          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 1.15/1.35          | (v2_funct_1 @ X16)
% 1.15/1.35          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.15/1.35      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.15/1.35  thf('63', plain,
% 1.15/1.35      (((v2_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | ~ (v1_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['61', '62'])).
% 1.15/1.35  thf('64', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('65', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('66', plain, ((v2_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.15/1.35  thf('67', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('68', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(cc1_relset_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.35       ( v1_relat_1 @ C ) ))).
% 1.15/1.35  thf('69', plain,
% 1.15/1.35      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.15/1.35         ((v1_relat_1 @ X2)
% 1.15/1.35          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.15/1.35      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.15/1.35  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 1.15/1.35      inference('sup-', [status(thm)], ['68', '69'])).
% 1.15/1.35  thf('71', plain,
% 1.15/1.35      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35        (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ (k6_partfun1 @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['58', '59', '60', '66', '67', '70'])).
% 1.15/1.35  thf('72', plain,
% 1.15/1.35      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.15/1.35         (k6_partfun1 @ sk_A)))),
% 1.15/1.35      inference('demod', [status(thm)], ['38', '71'])).
% 1.15/1.35  thf('73', plain,
% 1.15/1.35      (~
% 1.15/1.35       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.35          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35         (k6_partfun1 @ sk_A))) | 
% 1.15/1.35       ~
% 1.15/1.35       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.15/1.35          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.15/1.35         (k6_partfun1 @ sk_A)))),
% 1.15/1.35      inference('split', [status(esa)], ['0'])).
% 1.15/1.35  thf('74', plain,
% 1.15/1.35      (~
% 1.15/1.35       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.35          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35         (k6_partfun1 @ sk_A)))),
% 1.15/1.35      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 1.15/1.35  thf('75', plain,
% 1.15/1.35      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.15/1.35           sk_B_1) @ 
% 1.15/1.35          (k6_partfun1 @ sk_A))),
% 1.15/1.35      inference('simpl_trail', [status(thm)], ['9', '74'])).
% 1.15/1.35  thf('76', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('77', plain,
% 1.15/1.35      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 1.15/1.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 1.15/1.35  thf('78', plain,
% 1.15/1.35      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.35         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.15/1.35          | ~ (v1_funct_1 @ X23)
% 1.15/1.35          | ~ (v1_funct_1 @ X26)
% 1.15/1.35          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.15/1.35          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 1.15/1.35              = (k5_relat_1 @ X23 @ X26)))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.15/1.35  thf('79', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 1.15/1.35            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 1.15/1.35            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X0)
% 1.15/1.35          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['77', '78'])).
% 1.15/1.35  thf('80', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 1.15/1.35  thf('81', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 1.15/1.35            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 1.15/1.35            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X0))),
% 1.15/1.35      inference('demod', [status(thm)], ['79', '80'])).
% 1.15/1.35  thf('82', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.35  thf('83', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.35  thf('84', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 1.15/1.35            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X0))),
% 1.15/1.35      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.15/1.35  thf('85', plain,
% 1.15/1.35      ((~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.15/1.35            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['76', '84'])).
% 1.15/1.35  thf('86', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('87', plain,
% 1.15/1.35      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.15/1.35         sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 1.15/1.35      inference('demod', [status(thm)], ['85', '86'])).
% 1.15/1.35  thf('88', plain,
% 1.15/1.35      (![X1 : $i]:
% 1.15/1.35         (~ (v2_funct_1 @ X1)
% 1.15/1.35          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 1.15/1.35              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X1)
% 1.15/1.35          | ~ (v1_relat_1 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.15/1.35  thf('89', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.35  thf('90', plain,
% 1.15/1.35      (![X1 : $i]:
% 1.15/1.35         (~ (v2_funct_1 @ X1)
% 1.15/1.35          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 1.15/1.35              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X1)
% 1.15/1.35          | ~ (v1_relat_1 @ X1))),
% 1.15/1.35      inference('demod', [status(thm)], ['88', '89'])).
% 1.15/1.35  thf('91', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('92', plain,
% 1.15/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.15/1.35         (~ (v1_funct_1 @ X16)
% 1.15/1.35          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 1.15/1.35          | (v2_funct_2 @ X16 @ X18)
% 1.15/1.35          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.15/1.35      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.15/1.35  thf('93', plain,
% 1.15/1.35      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 1.15/1.35        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.15/1.35        | ~ (v1_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['91', '92'])).
% 1.15/1.35  thf('94', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('95', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('96', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 1.15/1.35      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.15/1.35  thf(d3_funct_2, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.15/1.35       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.15/1.35  thf('97', plain,
% 1.15/1.35      (![X19 : $i, X20 : $i]:
% 1.15/1.35         (~ (v2_funct_2 @ X20 @ X19)
% 1.15/1.35          | ((k2_relat_1 @ X20) = (X19))
% 1.15/1.35          | ~ (v5_relat_1 @ X20 @ X19)
% 1.15/1.35          | ~ (v1_relat_1 @ X20))),
% 1.15/1.35      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.15/1.35  thf('98', plain,
% 1.15/1.35      ((~ (v1_relat_1 @ sk_B_1)
% 1.15/1.35        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 1.15/1.35        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['96', '97'])).
% 1.15/1.35  thf('99', plain, ((v1_relat_1 @ sk_B_1)),
% 1.15/1.35      inference('sup-', [status(thm)], ['68', '69'])).
% 1.15/1.35  thf('100', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(cc2_relset_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.35       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.15/1.35  thf('101', plain,
% 1.15/1.35      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.15/1.35         ((v5_relat_1 @ X5 @ X7)
% 1.15/1.35          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.15/1.35      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.35  thf('102', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 1.15/1.35      inference('sup-', [status(thm)], ['100', '101'])).
% 1.15/1.35  thf('103', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['98', '99', '102'])).
% 1.15/1.35  thf('104', plain,
% 1.15/1.35      (![X1 : $i]:
% 1.15/1.35         (~ (v2_funct_1 @ X1)
% 1.15/1.35          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 1.15/1.35              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 1.15/1.35          | ~ (v1_funct_1 @ X1)
% 1.15/1.35          | ~ (v1_relat_1 @ X1))),
% 1.15/1.35      inference('demod', [status(thm)], ['88', '89'])).
% 1.15/1.35  thf('105', plain,
% 1.15/1.35      (![X15 : $i]:
% 1.15/1.35         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.15/1.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.35      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.35  thf('106', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.15/1.35          | ~ (v1_relat_1 @ X0)
% 1.15/1.35          | ~ (v1_funct_1 @ X0)
% 1.15/1.35          | ~ (v2_funct_1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['104', '105'])).
% 1.15/1.35  thf('107', plain,
% 1.15/1.35      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)))
% 1.15/1.35        | ~ (v2_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_relat_1 @ sk_B_1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['103', '106'])).
% 1.15/1.35  thf('108', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['98', '99', '102'])).
% 1.15/1.35  thf('109', plain, ((v2_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.15/1.35  thf('110', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('111', plain, ((v1_relat_1 @ sk_B_1)),
% 1.15/1.35      inference('sup-', [status(thm)], ['68', '69'])).
% 1.15/1.35  thf('112', plain,
% 1.15/1.35      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.35      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 1.15/1.35  thf('113', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.15/1.35      inference('condensation', [status(thm)], ['54'])).
% 1.15/1.35  thf('114', plain,
% 1.15/1.35      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['112', '113'])).
% 1.15/1.35  thf('115', plain,
% 1.15/1.35      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35         (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.15/1.35         (k6_partfun1 @ (k2_relat_1 @ sk_B_1)))
% 1.15/1.35        | ~ (v1_relat_1 @ sk_B_1)
% 1.15/1.35        | ~ (v1_funct_1 @ sk_B_1)
% 1.15/1.35        | ~ (v2_funct_1 @ sk_B_1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['90', '114'])).
% 1.15/1.35  thf('116', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['98', '99', '102'])).
% 1.15/1.35  thf('117', plain, ((v1_relat_1 @ sk_B_1)),
% 1.15/1.35      inference('sup-', [status(thm)], ['68', '69'])).
% 1.15/1.35  thf('118', plain, ((v1_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('119', plain, ((v2_funct_1 @ sk_B_1)),
% 1.15/1.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.15/1.35  thf('120', plain,
% 1.15/1.35      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.35        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_partfun1 @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 1.15/1.35  thf('121', plain, ($false),
% 1.15/1.35      inference('demod', [status(thm)], ['75', '87', '120'])).
% 1.15/1.35  
% 1.15/1.35  % SZS output end Refutation
% 1.15/1.35  
% 1.15/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
