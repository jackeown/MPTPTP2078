%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ofKJD69JFx

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:17 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 748 expanded)
%              Number of leaves         :   43 ( 241 expanded)
%              Depth                    :   16
%              Number of atoms          : 1613 (16834 expanded)
%              Number of equality atoms :   65 ( 151 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_funct_2 @ X33 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('17',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7','21'])).

thf('23',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7','21'])).

thf('32',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k4_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7','21'])).

thf('43',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k4_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','20'])).

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
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('49',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('55',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X35 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X24 @ X25 ) @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7','21'])).

thf('67',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('69',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X14 @ ( k3_relset_1 @ X14 @ X15 @ X16 ) )
        = ( k2_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k3_relset_1 @ sk_A @ sk_A @ sk_B ) )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k3_relset_1 @ X12 @ X13 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('73',plain,
    ( ( k3_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('75',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('76',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['70','73','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['58','59','67','77'])).

thf('79',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','78'])).

thf('80',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','79'])).

thf('81',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7','21'])).

thf('82',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('85',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('86',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(t54_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ B @ D )
                  = ( k11_relat_1 @ C @ D ) ) )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ( r2_relset_1 @ X19 @ X19 @ X20 @ X18 )
      | ( ( k11_relat_1 @ X20 @ ( sk_D @ X18 @ X20 @ X19 ) )
       != ( k11_relat_1 @ X18 @ ( sk_D @ X18 @ X20 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ( r2_relset_1 @ X0 @ X0 @ X1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference(eq_res,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X0 @ X0 @ X1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','91'])).

thf('93',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['23','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_relat_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('104',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('105',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('106',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('107',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('110',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('112',plain,
    ( ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X35 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('119',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('120',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['115','116','117','120'])).

thf('122',plain,
    ( ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['112','121'])).

thf('123',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_relat_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['95','123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ofKJD69JFx
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 278 iterations in 0.133s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.56  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.38/0.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.38/0.56  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.38/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.56  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.56  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(t88_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.56         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.56       ( ( r2_relset_1 @
% 0.38/0.56           A @ A @ 
% 0.38/0.56           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.38/0.56           ( k6_partfun1 @ A ) ) & 
% 0.38/0.56         ( r2_relset_1 @
% 0.38/0.56           A @ A @ 
% 0.38/0.56           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.38/0.56           ( k6_partfun1 @ A ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.56            ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.56            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.56          ( ( r2_relset_1 @
% 0.38/0.56              A @ A @ 
% 0.38/0.56              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.38/0.56              ( k6_partfun1 @ A ) ) & 
% 0.38/0.56            ( r2_relset_1 @
% 0.38/0.56              A @ A @ 
% 0.38/0.56              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.38/0.56              ( k6_partfun1 @ A ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.38/0.56           (k6_partfun1 @ sk_A))
% 0.38/0.56        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.38/0.56              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.56             (k6_partfun1 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.38/0.56           (k6_partfun1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.38/0.56               (k6_partfun1 @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k2_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.56         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.56       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i]:
% 0.38/0.56         (((k2_funct_2 @ X33 @ X32) = (k2_funct_1 @ X32))
% 0.38/0.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.38/0.56          | ~ (v3_funct_2 @ X32 @ X33 @ X33)
% 0.38/0.56          | ~ (v1_funct_2 @ X32 @ X33 @ X33)
% 0.38/0.56          | ~ (v1_funct_1 @ X32))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d9_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X0)
% 0.38/0.56          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.56        | ((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))
% 0.38/0.56        | ~ (v2_funct_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( v1_relat_1 @ C ) ))).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         ((v1_relat_1 @ X2)
% 0.38/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.56  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      ((((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B)) | ~ (v2_funct_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['10', '13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc2_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.56         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.56         (~ (v1_funct_1 @ X21)
% 0.38/0.56          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.38/0.56          | (v2_funct_1 @ X21)
% 0.38/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (((v2_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('20', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.56      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.56  thf('21', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '20'])).
% 0.38/0.56  thf('22', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5', '6', '7', '21'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56            (k4_relat_1 @ sk_B)) @ 
% 0.38/0.56           (k6_partfun1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.38/0.56               (k6_partfun1 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_k2_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.56         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.56       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.38/0.56         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.38/0.56         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.38/0.56         ( m1_subset_1 @
% 0.38/0.56           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k2_funct_2 @ X24 @ X25) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.38/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.38/0.56          | ~ (v3_funct_2 @ X25 @ X24 @ X24)
% 0.38/0.56          | ~ (v1_funct_2 @ X25 @ X24 @ X24)
% 0.38/0.56          | ~ (v1_funct_1 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('29', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('30', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5', '6', '7', '21'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((m1_subset_1 @ (k4_relat_1 @ sk_B) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.38/0.56  thf(redefinition_k1_partfun1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.56         ( v1_funct_1 @ F ) & 
% 0.38/0.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.38/0.56          | ~ (v1_funct_1 @ X26)
% 0.38/0.56          | ~ (v1_funct_1 @ X29)
% 0.38/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.38/0.56          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 0.38/0.56              = (k5_relat_1 @ X26 @ X29)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k4_relat_1 @ sk_B) @ X0)
% 0.38/0.56            = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i]:
% 0.38/0.56         ((v1_funct_1 @ (k2_funct_2 @ X24 @ X25))
% 0.38/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.38/0.56          | ~ (v3_funct_2 @ X25 @ X24 @ X24)
% 0.38/0.56          | ~ (v1_funct_2 @ X25 @ X24 @ X24)
% 0.38/0.56          | ~ (v1_funct_1 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('39', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('40', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('41', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.38/0.56  thf('42', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5', '6', '7', '21'])).
% 0.38/0.56  thf('43', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k4_relat_1 @ sk_B) @ X0)
% 0.38/0.56            = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['34', '43'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k4_relat_1 @ sk_B) @ 
% 0.38/0.56            sk_B) = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['24', '44'])).
% 0.38/0.56  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('47', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '20'])).
% 0.38/0.56  thf(t61_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ( v2_funct_1 @ A ) =>
% 0.38/0.56         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.38/0.56             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.38/0.56           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.38/0.56             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X1)
% 0.38/0.56          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.38/0.56              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.56  thf(redefinition_k6_partfun1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.38/0.56  thf('49', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X1)
% 0.38/0.56          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.38/0.56              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      ((((k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)
% 0.38/0.56          = (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v2_funct_1 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['47', '50'])).
% 0.38/0.56  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('54', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.56      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (((k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)
% 0.38/0.56         = (k6_partfun1 @ (k2_relat_1 @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      ((m1_subset_1 @ (k4_relat_1 @ sk_B) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.38/0.56  thf(t67_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.56       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (![X35 : $i, X36 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X35 @ X35 @ X36) = (X35))
% 0.38/0.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.38/0.56          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.38/0.56          | ~ (v1_funct_1 @ X36))),
% 0.38/0.56      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.38/0.56        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_B) @ sk_A @ sk_A)
% 0.38/0.56        | ((k1_relset_1 @ sk_A @ sk_A @ (k4_relat_1 @ sk_B)) = (sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.56  thf('59', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i]:
% 0.38/0.56         ((v1_funct_2 @ (k2_funct_2 @ X24 @ X25) @ X24 @ X24)
% 0.38/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.38/0.56          | ~ (v3_funct_2 @ X25 @ X24 @ X24)
% 0.38/0.56          | ~ (v1_funct_2 @ X25 @ X24 @ X24)
% 0.38/0.56          | ~ (v1_funct_1 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.56  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('64', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('65', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('66', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5', '6', '7', '21'])).
% 0.38/0.56  thf('67', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_B) @ sk_A @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t24_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.38/0.56           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.38/0.56         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.38/0.56           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X15 @ X14 @ (k3_relset_1 @ X14 @ X15 @ X16))
% 0.38/0.56            = (k2_relset_1 @ X14 @ X15 @ X16))
% 0.38/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.38/0.56      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (((k1_relset_1 @ sk_A @ sk_A @ (k3_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.38/0.56         = (k2_relset_1 @ sk_A @ sk_A @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.56  thf('71', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k3_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.56         (((k3_relset_1 @ X12 @ X13 @ X11) = (k4_relat_1 @ X11))
% 0.38/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      (((k3_relset_1 @ sk_A @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.56  thf('74', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.56         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      (((k1_relset_1 @ sk_A @ sk_A @ (k4_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['70', '73', '76'])).
% 0.38/0.56  thf('78', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['58', '59', '67', '77'])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      (((k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) = (k6_partfun1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['55', '78'])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k4_relat_1 @ sk_B) @ sk_B)
% 0.38/0.56         = (k6_partfun1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['45', '46', '79'])).
% 0.38/0.56  thf('81', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5', '6', '7', '21'])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.38/0.56            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.56           (k6_partfun1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.38/0.56                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.56               (k6_partfun1 @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k4_relat_1 @ sk_B) @ 
% 0.38/0.56            sk_B) @ 
% 0.38/0.56           (k6_partfun1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.38/0.56                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.56               (k6_partfun1 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.38/0.56  thf('84', plain,
% 0.38/0.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.38/0.56           (k6_partfun1 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.38/0.56                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.56               (k6_partfun1 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['80', '83'])).
% 0.38/0.56  thf(t29_relset_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( m1_subset_1 @
% 0.38/0.56       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (![X17 : $i]:
% 0.38/0.56         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.38/0.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.38/0.56  thf('86', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      (![X17 : $i]:
% 0.38/0.56         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.38/0.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.38/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.38/0.56  thf(t54_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.38/0.56           ( ( ![D:$i]:
% 0.38/0.56               ( ( r2_hidden @ D @ A ) =>
% 0.38/0.56                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.38/0.56             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.38/0.56          | (r2_relset_1 @ X19 @ X19 @ X20 @ X18)
% 0.38/0.56          | ((k11_relat_1 @ X20 @ (sk_D @ X18 @ X20 @ X19))
% 0.38/0.56              != (k11_relat_1 @ X18 @ (sk_D @ X18 @ X20 @ X19)))
% 0.38/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19))))),
% 0.38/0.56      inference('cnf', [status(esa)], [t54_relset_1])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 0.38/0.56          | (r2_relset_1 @ X0 @ X0 @ X1 @ X1)
% 0.38/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 0.38/0.56      inference('eq_res', [status(thm)], ['88'])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r2_relset_1 @ X0 @ X0 @ X1 @ X1)
% 0.38/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['89'])).
% 0.38/0.56  thf('91', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['87', '90'])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.38/0.56          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.56         (k6_partfun1 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['84', '91'])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      (~
% 0.38/0.56       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.38/0.56         (k6_partfun1 @ sk_A))) | 
% 0.38/0.56       ~
% 0.38/0.56       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.38/0.56          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.56         (k6_partfun1 @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('94', plain,
% 0.38/0.56      (~
% 0.38/0.56       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.38/0.56         (k6_partfun1 @ sk_A)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.56          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_relat_1 @ sk_B)) @ 
% 0.38/0.56          (k6_partfun1 @ sk_A))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['23', '94'])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      ((m1_subset_1 @ (k4_relat_1 @ sk_B) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.38/0.56  thf('97', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.38/0.56          | ~ (v1_funct_1 @ X26)
% 0.38/0.56          | ~ (v1_funct_1 @ X29)
% 0.38/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.38/0.56          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 0.38/0.56              = (k5_relat_1 @ X26 @ X29)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.38/0.56  thf('99', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.38/0.56            = (k5_relat_1 @ sk_B @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['97', '98'])).
% 0.38/0.56  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('101', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.38/0.56            = (k5_relat_1 @ sk_B @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['99', '100'])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.38/0.56        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.56            (k4_relat_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['96', '101'])).
% 0.38/0.56  thf('103', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('104', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '20'])).
% 0.38/0.56  thf('105', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X1)
% 0.38/0.56          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.38/0.56              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.56  thf('106', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.56  thf('107', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X1)
% 0.38/0.56          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.38/0.56              = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.38/0.56  thf('108', plain,
% 0.38/0.56      ((((k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))
% 0.38/0.56          = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v2_funct_1 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['104', '107'])).
% 0.38/0.56  thf('109', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('110', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('111', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.56      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.56  thf('112', plain,
% 0.38/0.56      (((k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))
% 0.38/0.56         = (k6_partfun1 @ (k1_relat_1 @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.38/0.56  thf('113', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('114', plain,
% 0.38/0.56      (![X35 : $i, X36 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X35 @ X35 @ X36) = (X35))
% 0.38/0.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.38/0.56          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.38/0.56          | ~ (v1_funct_1 @ X36))),
% 0.38/0.56      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.38/0.56  thf('115', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.56        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['113', '114'])).
% 0.38/0.56  thf('116', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('117', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('118', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('119', plain,
% 0.38/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.38/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.56  thf('120', plain,
% 0.38/0.56      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['118', '119'])).
% 0.38/0.56  thf('121', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['115', '116', '117', '120'])).
% 0.38/0.56  thf('122', plain,
% 0.38/0.56      (((k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) = (k6_partfun1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['112', '121'])).
% 0.38/0.56  thf('123', plain,
% 0.38/0.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_relat_1 @ sk_B))
% 0.38/0.56         = (k6_partfun1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['102', '103', '122'])).
% 0.38/0.56  thf('124', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['87', '90'])).
% 0.38/0.56  thf('125', plain, ($false),
% 0.38/0.56      inference('demod', [status(thm)], ['95', '123', '124'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
