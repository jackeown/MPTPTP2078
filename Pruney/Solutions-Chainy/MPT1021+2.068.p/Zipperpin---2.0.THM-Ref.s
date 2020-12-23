%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k2VRuNqhnT

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:22 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 457 expanded)
%              Number of leaves         :   39 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          : 1540 (9938 expanded)
%              Number of equality atoms :   43 (  73 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_funct_2 @ X32 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('39',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('61',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('63',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('70',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('76',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','73','74','75'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('77',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['43','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('82',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('83',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('85',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('88',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('91',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('100',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('101',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','102'])).

thf('104',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('106',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X34 @ X35 )
        = X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('111',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('112',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['107','108','109','112'])).

thf('114',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('116',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('118',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['104','113','116','117','118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k2VRuNqhnT
% 0.15/0.37  % Computer   : n016.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:25:04 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 622 iterations in 0.414s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.87  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.68/0.87  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.68/0.87  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.68/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.68/0.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.87  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.68/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.87  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.68/0.87  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.68/0.87  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.68/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.87  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.68/0.87  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.68/0.87  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.68/0.87  thf(t61_funct_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.87       ( ( v2_funct_1 @ A ) =>
% 0.68/0.87         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.68/0.87             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.68/0.87           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.68/0.87             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.68/0.87  thf('0', plain,
% 0.68/0.87      (![X5 : $i]:
% 0.68/0.87         (~ (v2_funct_1 @ X5)
% 0.68/0.87          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.68/0.87              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.68/0.87          | ~ (v1_funct_1 @ X5)
% 0.68/0.87          | ~ (v1_relat_1 @ X5))),
% 0.68/0.87      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.68/0.87  thf(t88_funct_2, conjecture,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.68/0.87         ( v3_funct_2 @ B @ A @ A ) & 
% 0.68/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.68/0.87       ( ( r2_relset_1 @
% 0.68/0.87           A @ A @ 
% 0.68/0.87           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.68/0.87           ( k6_partfun1 @ A ) ) & 
% 0.68/0.87         ( r2_relset_1 @
% 0.68/0.87           A @ A @ 
% 0.68/0.87           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.68/0.87           ( k6_partfun1 @ A ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i,B:$i]:
% 0.68/0.87        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.68/0.87            ( v3_funct_2 @ B @ A @ A ) & 
% 0.68/0.87            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.68/0.87          ( ( r2_relset_1 @
% 0.68/0.87              A @ A @ 
% 0.68/0.87              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.68/0.87              ( k6_partfun1 @ A ) ) & 
% 0.68/0.87            ( r2_relset_1 @
% 0.68/0.87              A @ A @ 
% 0.68/0.87              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.68/0.87              ( k6_partfun1 @ A ) ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.68/0.87  thf('1', plain,
% 0.68/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.68/0.87            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.68/0.87           (k6_partfun1 @ sk_A))
% 0.68/0.87        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.68/0.87              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.68/0.87             (k6_partfun1 @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.68/0.87            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.68/0.87           (k6_partfun1 @ sk_A)))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.68/0.87                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.68/0.87               (k6_partfun1 @ sk_A))))),
% 0.68/0.87      inference('split', [status(esa)], ['1'])).
% 0.68/0.87  thf(redefinition_k6_partfun1, axiom,
% 0.68/0.87    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.68/0.87  thf('3', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.68/0.87  thf('4', plain,
% 0.68/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.68/0.87            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.68/0.87           (k6_relat_1 @ sk_A)))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.68/0.87                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.68/0.87               (k6_partfun1 @ sk_A))))),
% 0.68/0.87      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(redefinition_k2_funct_2, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.68/0.87         ( v3_funct_2 @ B @ A @ A ) & 
% 0.68/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.68/0.87       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (![X31 : $i, X32 : $i]:
% 0.68/0.87         (((k2_funct_2 @ X32 @ X31) = (k2_funct_1 @ X31))
% 0.68/0.87          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.68/0.87          | ~ (v3_funct_2 @ X31 @ X32 @ X32)
% 0.68/0.87          | ~ (v1_funct_2 @ X31 @ X32 @ X32)
% 0.68/0.87          | ~ (v1_funct_1 @ X31))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.68/0.87  thf('7', plain,
% 0.68/0.87      ((~ (v1_funct_1 @ sk_B_1)
% 0.68/0.87        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.68/0.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.68/0.87        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.87  thf('8', plain, ((v1_funct_1 @ sk_B_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('9', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('10', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.68/0.87            (k2_funct_1 @ sk_B_1)) @ 
% 0.68/0.87           (k6_relat_1 @ sk_A)))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.68/0.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.68/0.87                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.68/0.87               (k6_partfun1 @ sk_A))))),
% 0.68/0.87      inference('demod', [status(thm)], ['4', '11'])).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('14', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(dt_k2_funct_2, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.68/0.87         ( v3_funct_2 @ B @ A @ A ) & 
% 0.68/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.68/0.87       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.68/0.87         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.68/0.87         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.68/0.87         ( m1_subset_1 @
% 0.68/0.87           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.68/0.87  thf('15', plain,
% 0.68/0.87      (![X21 : $i, X22 : $i]:
% 0.68/0.87         ((m1_subset_1 @ (k2_funct_2 @ X21 @ X22) @ 
% 0.68/0.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.68/0.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.68/0.87          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.68/0.87          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.68/0.87          | ~ (v1_funct_1 @ X22))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      ((~ (v1_funct_1 @ sk_B_1)
% 0.68/0.87        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.68/0.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.68/0.87        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.68/0.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.87  thf('17', plain, ((v1_funct_1 @ sk_B_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('18', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('19', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('20', plain,
% 0.68/0.87      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.68/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.68/0.87  thf(redefinition_k1_partfun1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.68/0.87     ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.68/0.87         ( v1_funct_1 @ F ) & 
% 0.68/0.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.68/0.87       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.68/0.87          | ~ (v1_funct_1 @ X25)
% 0.68/0.87          | ~ (v1_funct_1 @ X28)
% 0.68/0.87          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.68/0.87          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.68/0.87              = (k5_relat_1 @ X25 @ X28)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.68/0.87  thf('22', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 0.68/0.87            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 0.68/0.87            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.68/0.87          | ~ (v1_funct_1 @ X0)
% 0.68/0.87          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.87  thf('23', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('24', plain,
% 0.68/0.87      (![X21 : $i, X22 : $i]:
% 0.68/0.87         ((v1_funct_1 @ (k2_funct_2 @ X21 @ X22))
% 0.68/0.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.68/0.87          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.68/0.87          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.68/0.87          | ~ (v1_funct_1 @ X22))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.68/0.87  thf('25', plain,
% 0.68/0.87      ((~ (v1_funct_1 @ sk_B_1)
% 0.68/0.87        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.68/0.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.68/0.87        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.87  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('27', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('28', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.68/0.87  thf('30', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 0.71/0.87            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 0.71/0.87            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 0.71/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.87          | ~ (v1_funct_1 @ X0))),
% 0.71/0.87      inference('demod', [status(thm)], ['22', '29'])).
% 0.71/0.87  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.71/0.87  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.71/0.87  thf('33', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.87         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.71/0.87            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.71/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.87          | ~ (v1_funct_1 @ X0))),
% 0.71/0.87      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.71/0.87  thf('34', plain,
% 0.71/0.87      ((~ (v1_funct_1 @ sk_B_1)
% 0.71/0.87        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.71/0.87            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['13', '33'])).
% 0.71/0.87  thf('35', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('36', plain,
% 0.71/0.87      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.71/0.87         sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['34', '35'])).
% 0.71/0.87  thf('37', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.71/0.87  thf('38', plain,
% 0.71/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87           (k6_partfun1 @ sk_A)))
% 0.71/0.87         <= (~
% 0.71/0.87             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87               (k6_partfun1 @ sk_A))))),
% 0.71/0.87      inference('split', [status(esa)], ['1'])).
% 0.71/0.87  thf('39', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.71/0.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.87  thf('40', plain,
% 0.71/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87           (k6_relat_1 @ sk_A)))
% 0.71/0.87         <= (~
% 0.71/0.87             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87               (k6_partfun1 @ sk_A))))),
% 0.71/0.87      inference('demod', [status(thm)], ['38', '39'])).
% 0.71/0.87  thf('41', plain,
% 0.71/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.71/0.87            sk_B_1) @ 
% 0.71/0.87           (k6_relat_1 @ sk_A)))
% 0.71/0.87         <= (~
% 0.71/0.87             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87               (k6_partfun1 @ sk_A))))),
% 0.71/0.87      inference('sup-', [status(thm)], ['37', '40'])).
% 0.71/0.87  thf('42', plain,
% 0.71/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87           (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_relat_1 @ sk_A)))
% 0.71/0.87         <= (~
% 0.71/0.87             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87               (k6_partfun1 @ sk_A))))),
% 0.71/0.87      inference('sup-', [status(thm)], ['36', '41'])).
% 0.71/0.87  thf('43', plain,
% 0.71/0.87      (![X5 : $i]:
% 0.71/0.87         (~ (v2_funct_1 @ X5)
% 0.71/0.87          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.71/0.87              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.71/0.87          | ~ (v1_funct_1 @ X5)
% 0.71/0.87          | ~ (v1_relat_1 @ X5))),
% 0.71/0.87      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.71/0.87  thf('44', plain,
% 0.71/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(cc2_funct_2, axiom,
% 0.71/0.87    (![A:$i,B:$i,C:$i]:
% 0.71/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.87       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.71/0.87         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.71/0.87  thf('45', plain,
% 0.71/0.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.87         (~ (v1_funct_1 @ X16)
% 0.71/0.87          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.71/0.87          | (v2_funct_2 @ X16 @ X18)
% 0.71/0.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.71/0.87      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.71/0.87  thf('46', plain,
% 0.71/0.87      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 0.71/0.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.71/0.87        | ~ (v1_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['44', '45'])).
% 0.71/0.87  thf('47', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('48', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('49', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 0.71/0.87      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.71/0.87  thf(d3_funct_2, axiom,
% 0.71/0.87    (![A:$i,B:$i]:
% 0.71/0.87     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.71/0.87       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.71/0.87  thf('50', plain,
% 0.71/0.87      (![X19 : $i, X20 : $i]:
% 0.71/0.87         (~ (v2_funct_2 @ X20 @ X19)
% 0.71/0.87          | ((k2_relat_1 @ X20) = (X19))
% 0.71/0.87          | ~ (v5_relat_1 @ X20 @ X19)
% 0.71/0.87          | ~ (v1_relat_1 @ X20))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.71/0.87  thf('51', plain,
% 0.71/0.87      ((~ (v1_relat_1 @ sk_B_1)
% 0.71/0.87        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 0.71/0.87        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['49', '50'])).
% 0.71/0.87  thf('52', plain,
% 0.71/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(cc2_relat_1, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( v1_relat_1 @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.71/0.87  thf('53', plain,
% 0.71/0.87      (![X1 : $i, X2 : $i]:
% 0.71/0.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.71/0.87          | (v1_relat_1 @ X1)
% 0.71/0.87          | ~ (v1_relat_1 @ X2))),
% 0.71/0.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.71/0.87  thf('54', plain,
% 0.71/0.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['52', '53'])).
% 0.71/0.87  thf(fc6_relat_1, axiom,
% 0.71/0.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.71/0.87  thf('55', plain,
% 0.71/0.87      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.71/0.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.71/0.87  thf('56', plain, ((v1_relat_1 @ sk_B_1)),
% 0.71/0.87      inference('demod', [status(thm)], ['54', '55'])).
% 0.71/0.87  thf('57', plain,
% 0.71/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(cc2_relset_1, axiom,
% 0.71/0.87    (![A:$i,B:$i,C:$i]:
% 0.71/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.71/0.87  thf('58', plain,
% 0.71/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.71/0.87         ((v5_relat_1 @ X6 @ X8)
% 0.71/0.87          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.71/0.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.71/0.87  thf('59', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 0.71/0.87      inference('sup-', [status(thm)], ['57', '58'])).
% 0.71/0.87  thf('60', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.71/0.87  thf('61', plain,
% 0.71/0.87      (![X5 : $i]:
% 0.71/0.87         (~ (v2_funct_1 @ X5)
% 0.71/0.87          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.71/0.87              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.71/0.87          | ~ (v1_funct_1 @ X5)
% 0.71/0.87          | ~ (v1_relat_1 @ X5))),
% 0.71/0.87      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.71/0.87  thf(dt_k6_partfun1, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( m1_subset_1 @
% 0.71/0.87         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.71/0.87       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.71/0.87  thf('62', plain,
% 0.71/0.87      (![X24 : $i]:
% 0.71/0.87         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.71/0.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.71/0.87  thf('63', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.71/0.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.87  thf('64', plain,
% 0.71/0.87      (![X24 : $i]:
% 0.71/0.87         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.71/0.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.71/0.87      inference('demod', [status(thm)], ['62', '63'])).
% 0.71/0.87  thf('65', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.71/0.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.71/0.87          | ~ (v1_relat_1 @ X0)
% 0.71/0.87          | ~ (v1_funct_1 @ X0)
% 0.71/0.87          | ~ (v2_funct_1 @ X0))),
% 0.71/0.87      inference('sup+', [status(thm)], ['61', '64'])).
% 0.71/0.87  thf('66', plain,
% 0.71/0.87      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))
% 0.71/0.87        | ~ (v2_funct_1 @ sk_B_1)
% 0.71/0.87        | ~ (v1_funct_1 @ sk_B_1)
% 0.71/0.87        | ~ (v1_relat_1 @ sk_B_1))),
% 0.71/0.87      inference('sup+', [status(thm)], ['60', '65'])).
% 0.71/0.87  thf('67', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.71/0.87  thf('68', plain,
% 0.71/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('69', plain,
% 0.71/0.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.87         (~ (v1_funct_1 @ X16)
% 0.71/0.87          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.71/0.87          | (v2_funct_1 @ X16)
% 0.71/0.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.71/0.87      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.71/0.87  thf('70', plain,
% 0.71/0.87      (((v2_funct_1 @ sk_B_1)
% 0.71/0.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.71/0.87        | ~ (v1_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['68', '69'])).
% 0.71/0.87  thf('71', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('72', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('73', plain, ((v2_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.71/0.87  thf('74', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('75', plain, ((v1_relat_1 @ sk_B_1)),
% 0.71/0.87      inference('demod', [status(thm)], ['54', '55'])).
% 0.71/0.87  thf('76', plain,
% 0.71/0.87      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['66', '67', '73', '74', '75'])).
% 0.71/0.87  thf(reflexivity_r2_relset_1, axiom,
% 0.71/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.87     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.71/0.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.87       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.71/0.87  thf('77', plain,
% 0.71/0.87      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.71/0.87         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.71/0.87          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.71/0.87          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.71/0.87      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.71/0.87  thf('78', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.87         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.71/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.71/0.87      inference('condensation', [status(thm)], ['77'])).
% 0.71/0.87  thf('79', plain,
% 0.71/0.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['76', '78'])).
% 0.71/0.87  thf('80', plain,
% 0.71/0.87      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87         (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87         (k6_relat_1 @ (k2_relat_1 @ sk_B_1)))
% 0.71/0.87        | ~ (v1_relat_1 @ sk_B_1)
% 0.71/0.87        | ~ (v1_funct_1 @ sk_B_1)
% 0.71/0.87        | ~ (v2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('sup+', [status(thm)], ['43', '79'])).
% 0.71/0.87  thf('81', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.71/0.87  thf('82', plain, ((v1_relat_1 @ sk_B_1)),
% 0.71/0.87      inference('demod', [status(thm)], ['54', '55'])).
% 0.71/0.87  thf('83', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('84', plain, ((v2_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.71/0.87  thf('85', plain,
% 0.71/0.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_relat_1 @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.71/0.87  thf('86', plain,
% 0.71/0.87      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87         (k6_partfun1 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['42', '85'])).
% 0.71/0.87  thf('87', plain,
% 0.71/0.87      (~
% 0.71/0.87       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.71/0.87          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.71/0.87         (k6_partfun1 @ sk_A))) | 
% 0.71/0.87       ~
% 0.71/0.87       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.71/0.87          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.71/0.87         (k6_partfun1 @ sk_A)))),
% 0.71/0.87      inference('split', [status(esa)], ['1'])).
% 0.71/0.87  thf('88', plain,
% 0.71/0.87      (~
% 0.71/0.87       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.71/0.87          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.71/0.87         (k6_partfun1 @ sk_A)))),
% 0.71/0.87      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.71/0.87  thf('89', plain,
% 0.71/0.87      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.71/0.87           (k2_funct_1 @ sk_B_1)) @ 
% 0.71/0.87          (k6_relat_1 @ sk_A))),
% 0.71/0.87      inference('simpl_trail', [status(thm)], ['12', '88'])).
% 0.71/0.87  thf('90', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.71/0.87  thf('91', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.71/0.87  thf('92', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['90', '91'])).
% 0.71/0.87  thf('93', plain,
% 0.71/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('94', plain,
% 0.71/0.87      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.71/0.87         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.71/0.87          | ~ (v1_funct_1 @ X25)
% 0.71/0.87          | ~ (v1_funct_1 @ X28)
% 0.71/0.87          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.71/0.87          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.71/0.87              = (k5_relat_1 @ X25 @ X28)))),
% 0.71/0.87      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.71/0.87  thf('95', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.87         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.71/0.87            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.71/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.87          | ~ (v1_funct_1 @ X0)
% 0.71/0.87          | ~ (v1_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['93', '94'])).
% 0.71/0.87  thf('96', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('97', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.87         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.71/0.87            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.71/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.87          | ~ (v1_funct_1 @ X0))),
% 0.71/0.87      inference('demod', [status(thm)], ['95', '96'])).
% 0.71/0.87  thf('98', plain,
% 0.71/0.87      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.71/0.87        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.71/0.87            (k2_funct_1 @ sk_B_1))
% 0.71/0.87            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.71/0.87      inference('sup-', [status(thm)], ['92', '97'])).
% 0.71/0.87  thf('99', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.71/0.87  thf('100', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.71/0.87  thf('101', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['99', '100'])).
% 0.71/0.87  thf('102', plain,
% 0.71/0.87      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.71/0.87         (k2_funct_1 @ sk_B_1)) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.71/0.87      inference('demod', [status(thm)], ['98', '101'])).
% 0.71/0.87  thf('103', plain,
% 0.71/0.87      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.87          (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ (k6_relat_1 @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['89', '102'])).
% 0.71/0.87  thf('104', plain,
% 0.71/0.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B_1)) @ 
% 0.71/0.87           (k6_relat_1 @ sk_A))
% 0.71/0.87        | ~ (v1_relat_1 @ sk_B_1)
% 0.71/0.87        | ~ (v1_funct_1 @ sk_B_1)
% 0.71/0.87        | ~ (v2_funct_1 @ sk_B_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['0', '103'])).
% 0.71/0.87  thf('105', plain,
% 0.71/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(t67_funct_2, axiom,
% 0.71/0.87    (![A:$i,B:$i]:
% 0.71/0.87     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.71/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.71/0.87       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.71/0.87  thf('106', plain,
% 0.71/0.87      (![X34 : $i, X35 : $i]:
% 0.71/0.87         (((k1_relset_1 @ X34 @ X34 @ X35) = (X34))
% 0.71/0.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.71/0.87          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.71/0.87          | ~ (v1_funct_1 @ X35))),
% 0.71/0.87      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.71/0.87  thf('107', plain,
% 0.71/0.87      ((~ (v1_funct_1 @ sk_B_1)
% 0.71/0.87        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.71/0.87        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['105', '106'])).
% 0.71/0.87  thf('108', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('109', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('110', plain,
% 0.71/0.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.87    (![A:$i,B:$i,C:$i]:
% 0.71/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.87       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.87  thf('111', plain,
% 0.71/0.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.87         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.71/0.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.71/0.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.87  thf('112', plain,
% 0.71/0.87      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['110', '111'])).
% 0.71/0.87  thf('113', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['107', '108', '109', '112'])).
% 0.71/0.87  thf('114', plain,
% 0.71/0.87      (![X24 : $i]:
% 0.71/0.87         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.71/0.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.71/0.87      inference('demod', [status(thm)], ['62', '63'])).
% 0.71/0.87  thf('115', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.87         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.71/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.71/0.87      inference('condensation', [status(thm)], ['77'])).
% 0.71/0.87  thf('116', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['114', '115'])).
% 0.71/0.87  thf('117', plain, ((v1_relat_1 @ sk_B_1)),
% 0.71/0.87      inference('demod', [status(thm)], ['54', '55'])).
% 0.71/0.87  thf('118', plain, ((v1_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('119', plain, ((v2_funct_1 @ sk_B_1)),
% 0.71/0.87      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.71/0.87  thf('120', plain, ($false),
% 0.71/0.87      inference('demod', [status(thm)],
% 0.71/0.87                ['104', '113', '116', '117', '118', '119'])).
% 0.71/0.87  
% 0.71/0.87  % SZS output end Refutation
% 0.71/0.87  
% 0.71/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
