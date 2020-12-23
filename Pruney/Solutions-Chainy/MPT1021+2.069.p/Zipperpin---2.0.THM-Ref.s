%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wmYG6G0dwT

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:22 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 457 expanded)
%              Number of leaves         :   39 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          : 1540 (9938 expanded)
%              Number of equality atoms :   43 (  73 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_funct_2 @ X33 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','11'])).

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
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
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
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

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

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('39',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_2 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_2 @ X19 @ X18 )
      | ( ( k2_relat_1 @ X19 )
        = X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('61',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('63',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('70',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('76',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','73','74','75'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('77',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('85',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('88',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('91',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('100',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('101',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','102'])).

thf('104',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('106',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X35 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('111',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('112',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['107','108','109','112'])).

thf('114',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
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
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('118',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['104','113','116','117','118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wmYG6G0dwT
% 0.16/0.38  % Computer   : n007.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 11:50:36 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.90/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.16  % Solved by: fo/fo7.sh
% 0.90/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.16  % done 679 iterations in 0.673s
% 0.90/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.16  % SZS output start Refutation
% 0.90/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.16  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.90/1.16  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.90/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.16  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.90/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.16  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.16  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.90/1.16  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.16  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.90/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.16  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.90/1.16  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.16  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.16  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.16  thf(t61_funct_1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.16       ( ( v2_funct_1 @ A ) =>
% 0.90/1.16         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.90/1.16             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.90/1.16           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.90/1.16             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.16  thf('0', plain,
% 0.90/1.16      (![X4 : $i]:
% 0.90/1.16         (~ (v2_funct_1 @ X4)
% 0.90/1.16          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.90/1.16              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.90/1.16          | ~ (v1_funct_1 @ X4)
% 0.90/1.16          | ~ (v1_relat_1 @ X4))),
% 0.90/1.16      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.16  thf(t88_funct_2, conjecture,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.16         ( v3_funct_2 @ B @ A @ A ) & 
% 0.90/1.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.16       ( ( r2_relset_1 @
% 0.90/1.16           A @ A @ 
% 0.90/1.16           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.90/1.16           ( k6_partfun1 @ A ) ) & 
% 0.90/1.16         ( r2_relset_1 @
% 0.90/1.16           A @ A @ 
% 0.90/1.16           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.90/1.16           ( k6_partfun1 @ A ) ) ) ))).
% 0.90/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.16    (~( ![A:$i,B:$i]:
% 0.90/1.16        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.16            ( v3_funct_2 @ B @ A @ A ) & 
% 0.90/1.16            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.16          ( ( r2_relset_1 @
% 0.90/1.16              A @ A @ 
% 0.90/1.16              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.90/1.16              ( k6_partfun1 @ A ) ) & 
% 0.90/1.16            ( r2_relset_1 @
% 0.90/1.16              A @ A @ 
% 0.90/1.16              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.90/1.16              ( k6_partfun1 @ A ) ) ) ) )),
% 0.90/1.16    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.90/1.16  thf('1', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16           (k6_partfun1 @ sk_A))
% 0.90/1.16        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16             (k6_partfun1 @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('2', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16           (k6_partfun1 @ sk_A)))
% 0.90/1.16         <= (~
% 0.90/1.16             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16               (k6_partfun1 @ sk_A))))),
% 0.90/1.16      inference('split', [status(esa)], ['1'])).
% 0.90/1.16  thf(redefinition_k6_partfun1, axiom,
% 0.90/1.16    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.90/1.16  thf('3', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.16  thf('4', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16           (k6_relat_1 @ sk_A)))
% 0.90/1.16         <= (~
% 0.90/1.16             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16               (k6_partfun1 @ sk_A))))),
% 0.90/1.16      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.16  thf('5', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(redefinition_k2_funct_2, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.16         ( v3_funct_2 @ B @ A @ A ) & 
% 0.90/1.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.16       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.90/1.16  thf('6', plain,
% 0.90/1.16      (![X32 : $i, X33 : $i]:
% 0.90/1.16         (((k2_funct_2 @ X33 @ X32) = (k2_funct_1 @ X32))
% 0.90/1.16          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.90/1.16          | ~ (v3_funct_2 @ X32 @ X33 @ X33)
% 0.90/1.16          | ~ (v1_funct_2 @ X32 @ X33 @ X33)
% 0.90/1.16          | ~ (v1_funct_1 @ X32))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.90/1.16  thf('7', plain,
% 0.90/1.16      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.16  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.90/1.16  thf('12', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16            (k2_funct_1 @ sk_B)) @ 
% 0.90/1.16           (k6_relat_1 @ sk_A)))
% 0.90/1.16         <= (~
% 0.90/1.16             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16               (k6_partfun1 @ sk_A))))),
% 0.90/1.16      inference('demod', [status(thm)], ['4', '11'])).
% 0.90/1.16  thf('13', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('14', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(dt_k2_funct_2, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.16         ( v3_funct_2 @ B @ A @ A ) & 
% 0.90/1.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.16       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.90/1.16         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.90/1.16         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.90/1.16         ( m1_subset_1 @
% 0.90/1.16           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.90/1.16  thf('15', plain,
% 0.90/1.16      (![X20 : $i, X21 : $i]:
% 0.90/1.16         ((m1_subset_1 @ (k2_funct_2 @ X20 @ X21) @ 
% 0.90/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.90/1.16          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.90/1.16          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 0.90/1.16          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.90/1.16          | ~ (v1_funct_1 @ X21))),
% 0.90/1.16      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.90/1.16  thf('16', plain,
% 0.90/1.16      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.90/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.16  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('20', plain,
% 0.90/1.16      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.90/1.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.90/1.16  thf(redefinition_k1_partfun1, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.16     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.16         ( v1_funct_1 @ F ) & 
% 0.90/1.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.16       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.16  thf('21', plain,
% 0.90/1.16      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.90/1.16          | ~ (v1_funct_1 @ X26)
% 0.90/1.16          | ~ (v1_funct_1 @ X29)
% 0.90/1.16          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.90/1.16          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 0.90/1.16              = (k5_relat_1 @ X26 @ X29)))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.16  thf('22', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.90/1.16            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 0.90/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.16          | ~ (v1_funct_1 @ X0)
% 0.90/1.16          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.16  thf('23', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('24', plain,
% 0.90/1.16      (![X20 : $i, X21 : $i]:
% 0.90/1.16         ((v1_funct_1 @ (k2_funct_2 @ X20 @ X21))
% 0.90/1.16          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.90/1.16          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 0.90/1.16          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.90/1.16          | ~ (v1_funct_1 @ X21))),
% 0.90/1.16      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.90/1.16  thf('25', plain,
% 0.90/1.16      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.16  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.90/1.16  thf('30', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.90/1.16            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 0.90/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.16          | ~ (v1_funct_1 @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['22', '29'])).
% 0.90/1.16  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.90/1.16  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.90/1.16  thf('33', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.90/1.16            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.90/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.16          | ~ (v1_funct_1 @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.90/1.16  thf('34', plain,
% 0.90/1.16      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.90/1.16            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['13', '33'])).
% 0.90/1.16  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('36', plain,
% 0.90/1.16      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.90/1.16         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['34', '35'])).
% 0.90/1.16  thf('37', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.90/1.16  thf('38', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16           (k6_partfun1 @ sk_A)))
% 0.90/1.16         <= (~
% 0.90/1.16             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16               (k6_partfun1 @ sk_A))))),
% 0.90/1.16      inference('split', [status(esa)], ['1'])).
% 0.90/1.16  thf('39', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.16  thf('40', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16           (k6_relat_1 @ sk_A)))
% 0.90/1.16         <= (~
% 0.90/1.16             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16               (k6_partfun1 @ sk_A))))),
% 0.90/1.16      inference('demod', [status(thm)], ['38', '39'])).
% 0.90/1.16  thf('41', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.90/1.16            sk_B) @ 
% 0.90/1.16           (k6_relat_1 @ sk_A)))
% 0.90/1.16         <= (~
% 0.90/1.16             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16               (k6_partfun1 @ sk_A))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['37', '40'])).
% 0.90/1.16  thf('42', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 0.90/1.16         <= (~
% 0.90/1.16             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16               (k6_partfun1 @ sk_A))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['36', '41'])).
% 0.90/1.16  thf('43', plain,
% 0.90/1.16      (![X4 : $i]:
% 0.90/1.16         (~ (v2_funct_1 @ X4)
% 0.90/1.16          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.90/1.16              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.90/1.16          | ~ (v1_funct_1 @ X4)
% 0.90/1.16          | ~ (v1_relat_1 @ X4))),
% 0.90/1.16      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.16  thf('44', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(cc2_funct_2, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.16       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.90/1.16         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.90/1.16  thf('45', plain,
% 0.90/1.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.16         (~ (v1_funct_1 @ X15)
% 0.90/1.16          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.90/1.16          | (v2_funct_2 @ X15 @ X17)
% 0.90/1.16          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.90/1.16      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.90/1.16  thf('46', plain,
% 0.90/1.16      (((v2_funct_2 @ sk_B @ sk_A)
% 0.90/1.16        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | ~ (v1_funct_1 @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.16  thf('47', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('49', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.90/1.16      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.90/1.16  thf(d3_funct_2, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.90/1.16       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.90/1.16  thf('50', plain,
% 0.90/1.16      (![X18 : $i, X19 : $i]:
% 0.90/1.16         (~ (v2_funct_2 @ X19 @ X18)
% 0.90/1.16          | ((k2_relat_1 @ X19) = (X18))
% 0.90/1.16          | ~ (v5_relat_1 @ X19 @ X18)
% 0.90/1.16          | ~ (v1_relat_1 @ X19))),
% 0.90/1.16      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.90/1.16  thf('51', plain,
% 0.90/1.16      ((~ (v1_relat_1 @ sk_B)
% 0.90/1.16        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.90/1.16        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.16  thf('52', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(cc2_relat_1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( v1_relat_1 @ A ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.16  thf('53', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.90/1.16          | (v1_relat_1 @ X0)
% 0.90/1.16          | ~ (v1_relat_1 @ X1))),
% 0.90/1.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.16  thf('54', plain,
% 0.90/1.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['52', '53'])).
% 0.90/1.16  thf(fc6_relat_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.16  thf('55', plain,
% 0.90/1.16      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.90/1.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.16  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.16  thf('57', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(cc2_relset_1, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.16       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.90/1.16  thf('58', plain,
% 0.90/1.16      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.16         ((v5_relat_1 @ X5 @ X7)
% 0.90/1.16          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.90/1.16      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.16  thf('59', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.90/1.16      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.16  thf('60', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.90/1.16  thf('61', plain,
% 0.90/1.16      (![X4 : $i]:
% 0.90/1.16         (~ (v2_funct_1 @ X4)
% 0.90/1.16          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.90/1.16              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.90/1.16          | ~ (v1_funct_1 @ X4)
% 0.90/1.16          | ~ (v1_relat_1 @ X4))),
% 0.90/1.16      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.16  thf(dt_k6_partfun1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( m1_subset_1 @
% 0.90/1.16         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.90/1.16       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.90/1.16  thf('62', plain,
% 0.90/1.16      (![X23 : $i]:
% 0.90/1.16         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 0.90/1.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.90/1.16      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.16  thf('63', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.16  thf('64', plain,
% 0.90/1.16      (![X23 : $i]:
% 0.90/1.16         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.90/1.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.90/1.16      inference('demod', [status(thm)], ['62', '63'])).
% 0.90/1.16  thf('65', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.90/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.90/1.16          | ~ (v1_relat_1 @ X0)
% 0.90/1.16          | ~ (v1_funct_1 @ X0)
% 0.90/1.16          | ~ (v2_funct_1 @ X0))),
% 0.90/1.16      inference('sup+', [status(thm)], ['61', '64'])).
% 0.90/1.16  thf('66', plain,
% 0.90/1.16      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.90/1.16         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 0.90/1.16        | ~ (v2_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.16      inference('sup+', [status(thm)], ['60', '65'])).
% 0.90/1.16  thf('67', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.90/1.16  thf('68', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('69', plain,
% 0.90/1.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.16         (~ (v1_funct_1 @ X15)
% 0.90/1.16          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.90/1.16          | (v2_funct_1 @ X15)
% 0.90/1.16          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.90/1.16      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.90/1.16  thf('70', plain,
% 0.90/1.16      (((v2_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | ~ (v1_funct_1 @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['68', '69'])).
% 0.90/1.16  thf('71', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('73', plain, ((v2_funct_1 @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.90/1.16  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.16  thf('76', plain,
% 0.90/1.16      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.90/1.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('demod', [status(thm)], ['66', '67', '73', '74', '75'])).
% 0.90/1.16  thf(reflexivity_r2_relset_1, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.16     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.16       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.90/1.16  thf('77', plain,
% 0.90/1.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.16         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 0.90/1.16          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.90/1.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.90/1.16      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.90/1.16  thf('78', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.90/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.90/1.16      inference('condensation', [status(thm)], ['77'])).
% 0.90/1.16  thf('79', plain,
% 0.90/1.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.90/1.16        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['76', '78'])).
% 0.90/1.16  thf('80', plain,
% 0.90/1.16      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.90/1.16         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.90/1.16        | ~ (v1_relat_1 @ sk_B)
% 0.90/1.16        | ~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v2_funct_1 @ sk_B))),
% 0.90/1.16      inference('sup+', [status(thm)], ['43', '79'])).
% 0.90/1.16  thf('81', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['51', '56', '59'])).
% 0.90/1.16  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.16  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.90/1.16  thf('85', plain,
% 0.90/1.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.90/1.16  thf('86', plain,
% 0.90/1.16      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16         (k6_partfun1 @ sk_A)))),
% 0.90/1.16      inference('demod', [status(thm)], ['42', '85'])).
% 0.90/1.16  thf('87', plain,
% 0.90/1.16      (~
% 0.90/1.16       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16         (k6_partfun1 @ sk_A))) | 
% 0.90/1.16       ~
% 0.90/1.16       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.90/1.16          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.90/1.16         (k6_partfun1 @ sk_A)))),
% 0.90/1.16      inference('split', [status(esa)], ['1'])).
% 0.90/1.16  thf('88', plain,
% 0.90/1.16      (~
% 0.90/1.16       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.90/1.16         (k6_partfun1 @ sk_A)))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.90/1.16  thf('89', plain,
% 0.90/1.16      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.90/1.16          (k6_relat_1 @ sk_A))),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['12', '88'])).
% 0.90/1.16  thf('90', plain,
% 0.90/1.16      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.90/1.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.90/1.16  thf('91', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.90/1.16  thf('92', plain,
% 0.90/1.16      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.90/1.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('demod', [status(thm)], ['90', '91'])).
% 0.90/1.16  thf('93', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('94', plain,
% 0.90/1.16      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.90/1.16          | ~ (v1_funct_1 @ X26)
% 0.90/1.16          | ~ (v1_funct_1 @ X29)
% 0.90/1.16          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.90/1.16          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 0.90/1.16              = (k5_relat_1 @ X26 @ X29)))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.16  thf('95', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.90/1.16            = (k5_relat_1 @ sk_B @ X0))
% 0.90/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.16          | ~ (v1_funct_1 @ X0)
% 0.90/1.16          | ~ (v1_funct_1 @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['93', '94'])).
% 0.90/1.16  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('97', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.90/1.16            = (k5_relat_1 @ sk_B @ X0))
% 0.90/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.16          | ~ (v1_funct_1 @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['95', '96'])).
% 0.90/1.16  thf('98', plain,
% 0.90/1.16      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.90/1.16        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.16            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['92', '97'])).
% 0.90/1.16  thf('99', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.90/1.16  thf('100', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.90/1.16  thf('101', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['99', '100'])).
% 0.90/1.16  thf('102', plain,
% 0.90/1.16      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.90/1.16         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.90/1.16      inference('demod', [status(thm)], ['98', '101'])).
% 0.90/1.16  thf('103', plain,
% 0.90/1.16      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.16          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['89', '102'])).
% 0.90/1.16  thf('104', plain,
% 0.90/1.16      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.90/1.16           (k6_relat_1 @ sk_A))
% 0.90/1.16        | ~ (v1_relat_1 @ sk_B)
% 0.90/1.16        | ~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v2_funct_1 @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['0', '103'])).
% 0.90/1.16  thf('105', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(t67_funct_2, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.16       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.90/1.16  thf('106', plain,
% 0.90/1.16      (![X35 : $i, X36 : $i]:
% 0.90/1.16         (((k1_relset_1 @ X35 @ X35 @ X36) = (X35))
% 0.90/1.16          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.90/1.16          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.90/1.16          | ~ (v1_funct_1 @ X36))),
% 0.90/1.16      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.90/1.16  thf('107', plain,
% 0.90/1.16      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.16        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.16        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['105', '106'])).
% 0.90/1.16  thf('108', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('109', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('110', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.16       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.16  thf('111', plain,
% 0.90/1.16      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.16         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.90/1.16          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.16  thf('112', plain,
% 0.90/1.16      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['110', '111'])).
% 0.90/1.16  thf('113', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['107', '108', '109', '112'])).
% 0.90/1.16  thf('114', plain,
% 0.90/1.16      (![X23 : $i]:
% 0.90/1.16         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.90/1.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.90/1.16      inference('demod', [status(thm)], ['62', '63'])).
% 0.90/1.16  thf('115', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.90/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.90/1.16      inference('condensation', [status(thm)], ['77'])).
% 0.90/1.16  thf('116', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['114', '115'])).
% 0.90/1.16  thf('117', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.16  thf('118', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('119', plain, ((v2_funct_1 @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.90/1.16  thf('120', plain, ($false),
% 0.90/1.16      inference('demod', [status(thm)],
% 0.90/1.16                ['104', '113', '116', '117', '118', '119'])).
% 0.90/1.16  
% 0.90/1.16  % SZS output end Refutation
% 0.90/1.16  
% 0.90/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
