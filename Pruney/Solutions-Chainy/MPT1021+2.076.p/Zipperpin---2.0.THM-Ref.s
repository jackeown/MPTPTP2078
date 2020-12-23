%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UqTJHiiQ3s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:23 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 498 expanded)
%              Number of leaves         :   38 ( 166 expanded)
%              Depth                    :   12
%              Number of atoms          : 1537 (10857 expanded)
%              Number of equality atoms :   47 (  92 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X30: $i,X31: $i] :
      ( ( ( k2_funct_2 @ X31 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X33 @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('49',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('51',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('52',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('69',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','66','67','72'])).

thf('74',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','73'])).

thf('75',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('80',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('85',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('91',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_2 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('95',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['95','96','97'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('99',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_2 @ X21 @ X20 )
      | ( ( k2_relat_1 @ X21 )
        = X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('103',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('104',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['100','101','104'])).

thf('106',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('107',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['100','101','104'])).

thf('111',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('112',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('114',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('116',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['92','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['100','101','104'])).

thf('119',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('120',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('122',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['77','89','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UqTJHiiQ3s
% 0.15/0.36  % Computer   : n009.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 17:22:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 1.14/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.14/1.33  % Solved by: fo/fo7.sh
% 1.14/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.33  % done 1095 iterations in 0.856s
% 1.14/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.14/1.33  % SZS output start Refutation
% 1.14/1.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.33  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.14/1.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.14/1.33  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.14/1.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.14/1.33  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.14/1.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.14/1.33  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.14/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.33  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.14/1.33  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.14/1.33  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.14/1.33  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.14/1.33  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.14/1.33  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.14/1.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.33  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.14/1.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.14/1.33  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.14/1.33  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.14/1.33  thf(t88_funct_2, conjecture,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.14/1.33         ( v3_funct_2 @ B @ A @ A ) & 
% 1.14/1.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.14/1.33       ( ( r2_relset_1 @
% 1.14/1.33           A @ A @ 
% 1.14/1.33           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.14/1.33           ( k6_partfun1 @ A ) ) & 
% 1.14/1.33         ( r2_relset_1 @
% 1.14/1.33           A @ A @ 
% 1.14/1.33           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.14/1.33           ( k6_partfun1 @ A ) ) ) ))).
% 1.14/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.33    (~( ![A:$i,B:$i]:
% 1.14/1.33        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.14/1.33            ( v3_funct_2 @ B @ A @ A ) & 
% 1.14/1.33            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.14/1.33          ( ( r2_relset_1 @
% 1.14/1.33              A @ A @ 
% 1.14/1.33              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.14/1.33              ( k6_partfun1 @ A ) ) & 
% 1.14/1.33            ( r2_relset_1 @
% 1.14/1.33              A @ A @ 
% 1.14/1.33              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.14/1.33              ( k6_partfun1 @ A ) ) ) ) )),
% 1.14/1.33    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.14/1.33  thf('0', plain,
% 1.14/1.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.14/1.33           (k6_partfun1 @ sk_A))
% 1.14/1.33        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.14/1.33              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33             (k6_partfun1 @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('1', plain,
% 1.14/1.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.14/1.33            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33           (k6_partfun1 @ sk_A)))
% 1.14/1.33         <= (~
% 1.14/1.33             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.14/1.33                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33               (k6_partfun1 @ sk_A))))),
% 1.14/1.33      inference('split', [status(esa)], ['0'])).
% 1.14/1.33  thf('2', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(redefinition_k2_funct_2, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.14/1.33         ( v3_funct_2 @ B @ A @ A ) & 
% 1.14/1.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.14/1.33       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.14/1.33  thf('3', plain,
% 1.14/1.33      (![X30 : $i, X31 : $i]:
% 1.14/1.33         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 1.14/1.33          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.14/1.33          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 1.14/1.33          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 1.14/1.33          | ~ (v1_funct_1 @ X30))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.14/1.33  thf('4', plain,
% 1.14/1.33      ((~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['2', '3'])).
% 1.14/1.33  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('6', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('7', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.14/1.33  thf('9', plain,
% 1.14/1.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.14/1.33            sk_B_1) @ 
% 1.14/1.33           (k6_partfun1 @ sk_A)))
% 1.14/1.33         <= (~
% 1.14/1.33             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.14/1.33                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33               (k6_partfun1 @ sk_A))))),
% 1.14/1.33      inference('demod', [status(thm)], ['1', '8'])).
% 1.14/1.33  thf('10', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(dt_k2_funct_2, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.14/1.33         ( v3_funct_2 @ B @ A @ A ) & 
% 1.14/1.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.14/1.33       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.14/1.33         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.14/1.33         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.14/1.33         ( m1_subset_1 @
% 1.14/1.33           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.14/1.33  thf('11', plain,
% 1.14/1.33      (![X22 : $i, X23 : $i]:
% 1.14/1.33         ((m1_subset_1 @ (k2_funct_2 @ X22 @ X23) @ 
% 1.14/1.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 1.14/1.33          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 1.14/1.33          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 1.14/1.33          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 1.14/1.33          | ~ (v1_funct_1 @ X23))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.14/1.33  thf('12', plain,
% 1.14/1.33      ((~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 1.14/1.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.14/1.33      inference('sup-', [status(thm)], ['10', '11'])).
% 1.14/1.33  thf('13', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('14', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('15', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('16', plain,
% 1.14/1.33      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 1.14/1.33  thf('17', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.14/1.33  thf('18', plain,
% 1.14/1.33      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('demod', [status(thm)], ['16', '17'])).
% 1.14/1.33  thf('19', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(redefinition_k1_partfun1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.14/1.33     ( ( ( v1_funct_1 @ E ) & 
% 1.14/1.33         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.14/1.33         ( v1_funct_1 @ F ) & 
% 1.14/1.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.14/1.33       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.14/1.33  thf('20', plain,
% 1.14/1.33      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.14/1.33          | ~ (v1_funct_1 @ X24)
% 1.14/1.33          | ~ (v1_funct_1 @ X27)
% 1.14/1.33          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.14/1.33          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 1.14/1.33              = (k5_relat_1 @ X24 @ X27)))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.14/1.33  thf('21', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 1.14/1.33            = (k5_relat_1 @ sk_B_1 @ X0))
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.14/1.33          | ~ (v1_funct_1 @ X0)
% 1.14/1.33          | ~ (v1_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['19', '20'])).
% 1.14/1.33  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('23', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 1.14/1.33            = (k5_relat_1 @ sk_B_1 @ X0))
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.14/1.33          | ~ (v1_funct_1 @ X0))),
% 1.14/1.33      inference('demod', [status(thm)], ['21', '22'])).
% 1.14/1.33  thf('24', plain,
% 1.14/1.33      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 1.14/1.33        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33            (k2_funct_1 @ sk_B_1))
% 1.14/1.33            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 1.14/1.33      inference('sup-', [status(thm)], ['18', '23'])).
% 1.14/1.33  thf('25', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('26', plain,
% 1.14/1.33      (![X22 : $i, X23 : $i]:
% 1.14/1.33         ((v1_funct_1 @ (k2_funct_2 @ X22 @ X23))
% 1.14/1.33          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 1.14/1.33          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 1.14/1.33          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 1.14/1.33          | ~ (v1_funct_1 @ X23))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.14/1.33  thf('27', plain,
% 1.14/1.33      ((~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['25', '26'])).
% 1.14/1.33  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('29', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('30', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('31', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 1.14/1.33  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.14/1.33  thf('33', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['31', '32'])).
% 1.14/1.33  thf('34', plain,
% 1.14/1.33      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33         (k2_funct_1 @ sk_B_1)) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 1.14/1.33      inference('demod', [status(thm)], ['24', '33'])).
% 1.14/1.33  thf('35', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.14/1.33  thf('36', plain,
% 1.14/1.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.14/1.33           (k6_partfun1 @ sk_A)))
% 1.14/1.33         <= (~
% 1.14/1.33             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.14/1.33               (k6_partfun1 @ sk_A))))),
% 1.14/1.33      inference('split', [status(esa)], ['0'])).
% 1.14/1.33  thf('37', plain,
% 1.14/1.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33            (k2_funct_1 @ sk_B_1)) @ 
% 1.14/1.33           (k6_partfun1 @ sk_A)))
% 1.14/1.33         <= (~
% 1.14/1.33             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.14/1.33               (k6_partfun1 @ sk_A))))),
% 1.14/1.33      inference('sup-', [status(thm)], ['35', '36'])).
% 1.14/1.33  thf('38', plain,
% 1.14/1.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33           (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ (k6_partfun1 @ sk_A)))
% 1.14/1.33         <= (~
% 1.14/1.33             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.14/1.33               (k6_partfun1 @ sk_A))))),
% 1.14/1.33      inference('sup-', [status(thm)], ['34', '37'])).
% 1.14/1.33  thf('39', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(t67_funct_2, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.14/1.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.14/1.33       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.14/1.33  thf('40', plain,
% 1.14/1.33      (![X33 : $i, X34 : $i]:
% 1.14/1.33         (((k1_relset_1 @ X33 @ X33 @ X34) = (X33))
% 1.14/1.33          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 1.14/1.33          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 1.14/1.33          | ~ (v1_funct_1 @ X34))),
% 1.14/1.33      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.14/1.33  thf('41', plain,
% 1.14/1.33      ((~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['39', '40'])).
% 1.14/1.33  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('43', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('44', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(redefinition_k1_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.14/1.33  thf('45', plain,
% 1.14/1.33      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.14/1.33         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 1.14/1.33          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.14/1.33  thf('46', plain,
% 1.14/1.33      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['44', '45'])).
% 1.14/1.33  thf('47', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.14/1.33  thf(t61_funct_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.14/1.33       ( ( v2_funct_1 @ A ) =>
% 1.14/1.33         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.14/1.33             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.14/1.33           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.14/1.33             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.14/1.33  thf('48', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (~ (v2_funct_1 @ X5)
% 1.14/1.33          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 1.14/1.33              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 1.14/1.33          | ~ (v1_funct_1 @ X5)
% 1.14/1.33          | ~ (v1_relat_1 @ X5))),
% 1.14/1.33      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.14/1.33  thf(redefinition_k6_partfun1, axiom,
% 1.14/1.33    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.14/1.33  thf('49', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.14/1.33  thf('50', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (~ (v2_funct_1 @ X5)
% 1.14/1.33          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 1.14/1.33              = (k6_partfun1 @ (k1_relat_1 @ X5)))
% 1.14/1.33          | ~ (v1_funct_1 @ X5)
% 1.14/1.33          | ~ (v1_relat_1 @ X5))),
% 1.14/1.33      inference('demod', [status(thm)], ['48', '49'])).
% 1.14/1.33  thf(t29_relset_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( m1_subset_1 @
% 1.14/1.33       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.14/1.33  thf('51', plain,
% 1.14/1.33      (![X16 : $i]:
% 1.14/1.33         (m1_subset_1 @ (k6_relat_1 @ X16) @ 
% 1.14/1.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 1.14/1.33      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.14/1.33  thf('52', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.14/1.33  thf('53', plain,
% 1.14/1.33      (![X16 : $i]:
% 1.14/1.33         (m1_subset_1 @ (k6_partfun1 @ X16) @ 
% 1.14/1.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 1.14/1.33      inference('demod', [status(thm)], ['51', '52'])).
% 1.14/1.33  thf(reflexivity_r2_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.33     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.14/1.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.14/1.33       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 1.14/1.33  thf('54', plain,
% 1.14/1.33      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.14/1.33         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 1.14/1.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.14/1.33          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.14/1.33      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 1.14/1.33  thf('55', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.14/1.33      inference('condensation', [status(thm)], ['54'])).
% 1.14/1.33  thf('56', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['53', '55'])).
% 1.14/1.33  thf('57', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((r2_relset_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.14/1.33           (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 1.14/1.33           (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.14/1.33          | ~ (v1_relat_1 @ X0)
% 1.14/1.33          | ~ (v1_funct_1 @ X0)
% 1.14/1.33          | ~ (v2_funct_1 @ X0))),
% 1.14/1.33      inference('sup+', [status(thm)], ['50', '56'])).
% 1.14/1.33  thf('58', plain,
% 1.14/1.33      (((r2_relset_1 @ sk_A @ (k1_relat_1 @ sk_B_1) @ 
% 1.14/1.33         (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 1.14/1.33         (k6_partfun1 @ (k1_relat_1 @ sk_B_1)))
% 1.14/1.33        | ~ (v2_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_relat_1 @ sk_B_1))),
% 1.14/1.33      inference('sup+', [status(thm)], ['47', '57'])).
% 1.14/1.33  thf('59', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.14/1.33  thf('60', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 1.14/1.33  thf('61', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc2_funct_2, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.14/1.33         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.14/1.33  thf('62', plain,
% 1.14/1.33      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.14/1.33         (~ (v1_funct_1 @ X17)
% 1.14/1.33          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 1.14/1.33          | (v2_funct_1 @ X17)
% 1.14/1.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.14/1.33  thf('63', plain,
% 1.14/1.33      (((v2_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | ~ (v1_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['61', '62'])).
% 1.14/1.33  thf('64', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('65', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('66', plain, ((v2_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.14/1.33  thf('67', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('68', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc2_relat_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ A ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.14/1.33  thf('69', plain,
% 1.14/1.33      (![X1 : $i, X2 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 1.14/1.33          | (v1_relat_1 @ X1)
% 1.14/1.33          | ~ (v1_relat_1 @ X2))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.14/1.33  thf('70', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['68', '69'])).
% 1.14/1.33  thf(fc6_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.14/1.33  thf('71', plain,
% 1.14/1.33      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.14/1.33      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.14/1.33  thf('72', plain, ((v1_relat_1 @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['70', '71'])).
% 1.14/1.33  thf('73', plain,
% 1.14/1.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33        (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ (k6_partfun1 @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['58', '59', '60', '66', '67', '72'])).
% 1.14/1.33  thf('74', plain,
% 1.14/1.33      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.14/1.33         (k6_partfun1 @ sk_A)))),
% 1.14/1.33      inference('demod', [status(thm)], ['38', '73'])).
% 1.14/1.33  thf('75', plain,
% 1.14/1.33      (~
% 1.14/1.33       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.14/1.33          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33         (k6_partfun1 @ sk_A))) | 
% 1.14/1.33       ~
% 1.14/1.33       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 1.14/1.33          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 1.14/1.33         (k6_partfun1 @ sk_A)))),
% 1.14/1.33      inference('split', [status(esa)], ['0'])).
% 1.14/1.33  thf('76', plain,
% 1.14/1.33      (~
% 1.14/1.33       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.14/1.33          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33         (k6_partfun1 @ sk_A)))),
% 1.14/1.33      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 1.14/1.33  thf('77', plain,
% 1.14/1.33      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.14/1.33           sk_B_1) @ 
% 1.14/1.33          (k6_partfun1 @ sk_A))),
% 1.14/1.33      inference('simpl_trail', [status(thm)], ['9', '76'])).
% 1.14/1.33  thf('78', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('79', plain,
% 1.14/1.33      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 1.14/1.33  thf('80', plain,
% 1.14/1.33      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.14/1.33          | ~ (v1_funct_1 @ X24)
% 1.14/1.33          | ~ (v1_funct_1 @ X27)
% 1.14/1.33          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.14/1.33          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 1.14/1.33              = (k5_relat_1 @ X24 @ X27)))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.14/1.33  thf('81', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 1.14/1.33            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 1.14/1.33            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.14/1.33          | ~ (v1_funct_1 @ X0)
% 1.14/1.33          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['79', '80'])).
% 1.14/1.33  thf('82', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 1.14/1.33  thf('83', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 1.14/1.33            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 1.14/1.33            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.14/1.33          | ~ (v1_funct_1 @ X0))),
% 1.14/1.33      inference('demod', [status(thm)], ['81', '82'])).
% 1.14/1.33  thf('84', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.14/1.33  thf('85', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.14/1.33  thf('86', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 1.14/1.33            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.14/1.33          | ~ (v1_funct_1 @ X0))),
% 1.14/1.33      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.14/1.33  thf('87', plain,
% 1.14/1.33      ((~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.14/1.33            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['78', '86'])).
% 1.14/1.33  thf('88', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('89', plain,
% 1.14/1.33      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 1.14/1.33         sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['87', '88'])).
% 1.14/1.33  thf('90', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (~ (v2_funct_1 @ X5)
% 1.14/1.33          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 1.14/1.33              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 1.14/1.33          | ~ (v1_funct_1 @ X5)
% 1.14/1.33          | ~ (v1_relat_1 @ X5))),
% 1.14/1.33      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.14/1.33  thf('91', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.14/1.33  thf('92', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (~ (v2_funct_1 @ X5)
% 1.14/1.33          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 1.14/1.33              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 1.14/1.33          | ~ (v1_funct_1 @ X5)
% 1.14/1.33          | ~ (v1_relat_1 @ X5))),
% 1.14/1.33      inference('demod', [status(thm)], ['90', '91'])).
% 1.14/1.33  thf('93', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('94', plain,
% 1.14/1.33      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.14/1.33         (~ (v1_funct_1 @ X17)
% 1.14/1.33          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 1.14/1.33          | (v2_funct_2 @ X17 @ X19)
% 1.14/1.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.14/1.33  thf('95', plain,
% 1.14/1.33      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 1.14/1.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.14/1.33        | ~ (v1_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['93', '94'])).
% 1.14/1.33  thf('96', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('97', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('98', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 1.14/1.33      inference('demod', [status(thm)], ['95', '96', '97'])).
% 1.14/1.33  thf(d3_funct_2, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.14/1.33       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.14/1.33  thf('99', plain,
% 1.14/1.33      (![X20 : $i, X21 : $i]:
% 1.14/1.33         (~ (v2_funct_2 @ X21 @ X20)
% 1.14/1.33          | ((k2_relat_1 @ X21) = (X20))
% 1.14/1.33          | ~ (v5_relat_1 @ X21 @ X20)
% 1.14/1.33          | ~ (v1_relat_1 @ X21))),
% 1.14/1.33      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.14/1.33  thf('100', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ sk_B_1)
% 1.14/1.33        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 1.14/1.33        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['98', '99'])).
% 1.14/1.33  thf('101', plain, ((v1_relat_1 @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['70', '71'])).
% 1.14/1.33  thf('102', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc2_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.14/1.33  thf('103', plain,
% 1.14/1.33      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.14/1.33         ((v5_relat_1 @ X6 @ X8)
% 1.14/1.33          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.33  thf('104', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 1.14/1.33      inference('sup-', [status(thm)], ['102', '103'])).
% 1.14/1.33  thf('105', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['100', '101', '104'])).
% 1.14/1.33  thf('106', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (~ (v2_funct_1 @ X5)
% 1.14/1.33          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 1.14/1.33              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 1.14/1.33          | ~ (v1_funct_1 @ X5)
% 1.14/1.33          | ~ (v1_relat_1 @ X5))),
% 1.14/1.33      inference('demod', [status(thm)], ['90', '91'])).
% 1.14/1.33  thf('107', plain,
% 1.14/1.33      (![X16 : $i]:
% 1.14/1.33         (m1_subset_1 @ (k6_partfun1 @ X16) @ 
% 1.14/1.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 1.14/1.33      inference('demod', [status(thm)], ['51', '52'])).
% 1.14/1.33  thf('108', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.14/1.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.14/1.33          | ~ (v1_relat_1 @ X0)
% 1.14/1.33          | ~ (v1_funct_1 @ X0)
% 1.14/1.33          | ~ (v2_funct_1 @ X0))),
% 1.14/1.33      inference('sup+', [status(thm)], ['106', '107'])).
% 1.14/1.33  thf('109', plain,
% 1.14/1.33      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)))
% 1.14/1.33        | ~ (v2_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_relat_1 @ sk_B_1))),
% 1.14/1.33      inference('sup+', [status(thm)], ['105', '108'])).
% 1.14/1.33  thf('110', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['100', '101', '104'])).
% 1.14/1.33  thf('111', plain, ((v2_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.14/1.33  thf('112', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('113', plain, ((v1_relat_1 @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['70', '71'])).
% 1.14/1.33  thf('114', plain,
% 1.14/1.33      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.14/1.33      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.14/1.33  thf('115', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.14/1.33      inference('condensation', [status(thm)], ['54'])).
% 1.14/1.33  thf('116', plain,
% 1.14/1.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['114', '115'])).
% 1.14/1.33  thf('117', plain,
% 1.14/1.33      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33         (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 1.14/1.33         (k6_partfun1 @ (k2_relat_1 @ sk_B_1)))
% 1.14/1.33        | ~ (v1_relat_1 @ sk_B_1)
% 1.14/1.33        | ~ (v1_funct_1 @ sk_B_1)
% 1.14/1.33        | ~ (v2_funct_1 @ sk_B_1))),
% 1.14/1.33      inference('sup+', [status(thm)], ['92', '116'])).
% 1.14/1.33  thf('118', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['100', '101', '104'])).
% 1.14/1.33  thf('119', plain, ((v1_relat_1 @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['70', '71'])).
% 1.14/1.33  thf('120', plain, ((v1_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('121', plain, ((v2_funct_1 @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.14/1.33  thf('122', plain,
% 1.14/1.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.14/1.33        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_partfun1 @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 1.14/1.33  thf('123', plain, ($false),
% 1.14/1.33      inference('demod', [status(thm)], ['77', '89', '122'])).
% 1.14/1.33  
% 1.14/1.33  % SZS output end Refutation
% 1.14/1.33  
% 1.14/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
