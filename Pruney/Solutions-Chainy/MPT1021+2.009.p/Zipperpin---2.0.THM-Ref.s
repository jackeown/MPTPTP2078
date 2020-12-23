%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wLLLBiJ98P

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:11 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  191 (1503 expanded)
%              Number of leaves         :   37 ( 474 expanded)
%              Depth                    :   18
%              Number of atoms          : 1806 (37468 expanded)
%              Number of equality atoms :   63 ( 234 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

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
    ! [X34: $i,X35: $i] :
      ( ( ( k2_funct_2 @ X35 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X35 @ X35 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
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

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('38',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X24 @ X25 ) @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('52',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('54',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('55',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','67'])).

thf('69',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('70',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','67'])).

thf('71',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('75',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('77',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('80',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X37 @ X38 )
        = X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X24 @ X25 ) @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('92',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['83','84','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['80','93'])).

thf('95',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['77','94'])).

thf('96',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['76','95'])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','96'])).

thf('98',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('99',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('101',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('104',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('105',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('106',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('107',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','109'])).

thf('111',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('122',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('123',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('124',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('128',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('129',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('130',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('132',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130','131'])).

thf('133',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('134',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130','131'])).

thf('135',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X37 @ X38 )
        = X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('143',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['138','139','140','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('146',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('148',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','144','145','146','147'])).

thf('149',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['132','148'])).

thf('150',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['113','150','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wLLLBiJ98P
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 380 iterations in 0.236s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.72  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.49/0.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.72  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.49/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.72  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.49/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.49/0.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.49/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.72  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.49/0.72  thf(t88_funct_2, conjecture,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72       ( ( r2_relset_1 @
% 0.49/0.72           A @ A @ 
% 0.49/0.72           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.49/0.72           ( k6_partfun1 @ A ) ) & 
% 0.49/0.72         ( r2_relset_1 @
% 0.49/0.72           A @ A @ 
% 0.49/0.72           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.49/0.72           ( k6_partfun1 @ A ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i,B:$i]:
% 0.49/0.72        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72            ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.72            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72          ( ( r2_relset_1 @
% 0.49/0.72              A @ A @ 
% 0.49/0.72              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.49/0.72              ( k6_partfun1 @ A ) ) & 
% 0.49/0.72            ( r2_relset_1 @
% 0.49/0.72              A @ A @ 
% 0.49/0.72              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.49/0.72              ( k6_partfun1 @ A ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72           (k6_partfun1 @ sk_A))
% 0.49/0.72        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72             (k6_partfun1 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72           (k6_partfun1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf(redefinition_k6_partfun1, axiom,
% 0.49/0.72    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.49/0.72  thf('2', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72           (k6_relat_1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['1', '2'])).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(redefinition_k2_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X34 : $i, X35 : $i]:
% 0.49/0.72         (((k2_funct_2 @ X35 @ X34) = (k2_funct_1 @ X34))
% 0.49/0.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.49/0.72          | ~ (v3_funct_2 @ X34 @ X35 @ X35)
% 0.49/0.72          | ~ (v1_funct_2 @ X34 @ X35 @ X35)
% 0.49/0.72          | ~ (v1_funct_1 @ X34))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.72  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72            (k2_funct_1 @ sk_B)) @ 
% 0.49/0.72           (k6_relat_1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['3', '10'])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(dt_k2_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.49/0.72         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.49/0.72         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.49/0.72         ( m1_subset_1 @
% 0.49/0.72           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (![X24 : $i, X25 : $i]:
% 0.49/0.72         ((m1_subset_1 @ (k2_funct_2 @ X24 @ X25) @ 
% 0.49/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.49/0.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.49/0.72          | ~ (v3_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_1 @ X25))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.49/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.72  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.49/0.72  thf(redefinition_k1_partfun1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ E ) & 
% 0.49/0.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.72         ( v1_funct_1 @ F ) & 
% 0.49/0.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.49/0.72       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.49/0.72          | ~ (v1_funct_1 @ X28)
% 0.49/0.72          | ~ (v1_funct_1 @ X31)
% 0.49/0.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.49/0.72          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.49/0.72              = (k5_relat_1 @ X28 @ X31)))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.49/0.72            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.49/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.72  thf('23', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('24', plain,
% 0.49/0.72      (![X24 : $i, X25 : $i]:
% 0.49/0.72         ((v1_funct_1 @ (k2_funct_2 @ X24 @ X25))
% 0.49/0.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.49/0.72          | ~ (v3_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_1 @ X25))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.72  thf('25', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.72  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.49/0.72  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.49/0.72  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.72  thf('32', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.49/0.72            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.49/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.72          | ~ (v1_funct_1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['22', '31'])).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['12', '32'])).
% 0.49/0.72  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.49/0.72  thf(cc1_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( v1_relat_1 @ C ) ))).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.72         ((v1_relat_1 @ X11)
% 0.49/0.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.72  thf('37', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.72  thf(t65_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.49/0.72  thf('38', plain,
% 0.49/0.72      (![X10 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X10)
% 0.49/0.72          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.72  thf(t61_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v2_funct_1 @ A ) =>
% 0.49/0.72         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.49/0.72             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.49/0.72           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.49/0.72             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.72  thf('39', plain,
% 0.49/0.72      (![X8 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X8)
% 0.49/0.72          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.49/0.72              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.49/0.72          | ~ (v1_funct_1 @ X8)
% 0.49/0.72          | ~ (v1_relat_1 @ X8))),
% 0.49/0.72      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.49/0.72            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v2_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['38', '39'])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.72        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.72        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.49/0.72            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['37', '40'])).
% 0.49/0.72  thf('42', plain,
% 0.49/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.49/0.72  thf(cc2_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.49/0.72         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.72         (~ (v1_funct_1 @ X21)
% 0.49/0.72          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.49/0.72          | (v2_funct_1 @ X21)
% 0.49/0.72          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.72  thf('44', plain,
% 0.49/0.72      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.72        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.49/0.72        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.72  thf('45', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (![X24 : $i, X25 : $i]:
% 0.49/0.72         ((v3_funct_2 @ (k2_funct_2 @ X24 @ X25) @ X24 @ X24)
% 0.49/0.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.49/0.72          | ~ (v3_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_1 @ X25))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.72  thf('47', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.72  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('49', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('50', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('51', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.49/0.72  thf('52', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.49/0.72      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.49/0.72  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.72  thf('54', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.49/0.72  thf('55', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.72  thf('56', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('57', plain,
% 0.49/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.72         (~ (v1_funct_1 @ X21)
% 0.49/0.72          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.49/0.72          | (v2_funct_1 @ X21)
% 0.49/0.72          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.72  thf('58', plain,
% 0.49/0.72      (((v2_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.49/0.72  thf('59', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('61', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.49/0.72  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('63', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(cc2_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.49/0.72  thf('64', plain,
% 0.49/0.72      (![X4 : $i, X5 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.49/0.72          | (v1_relat_1 @ X4)
% 0.49/0.72          | ~ (v1_relat_1 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.72  thf('65', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['63', '64'])).
% 0.49/0.72  thf(fc6_relat_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.49/0.72  thf('66', plain,
% 0.49/0.72      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.72  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.49/0.72  thf('68', plain,
% 0.49/0.72      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.49/0.72         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('demod', [status(thm)], ['41', '54', '55', '61', '62', '67'])).
% 0.49/0.72  thf('69', plain,
% 0.49/0.72      (![X8 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X8)
% 0.49/0.72          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 0.49/0.72              = (k6_relat_1 @ (k2_relat_1 @ X8)))
% 0.49/0.72          | ~ (v1_funct_1 @ X8)
% 0.49/0.72          | ~ (v1_relat_1 @ X8))),
% 0.49/0.72      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.72  thf('70', plain,
% 0.49/0.72      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.49/0.72         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('demod', [status(thm)], ['41', '54', '55', '61', '62', '67'])).
% 0.49/0.72  thf('71', plain,
% 0.49/0.72      ((((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.49/0.72          = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v2_funct_1 @ sk_B))),
% 0.49/0.72      inference('sup+', [status(thm)], ['69', '70'])).
% 0.49/0.72  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.49/0.72  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.49/0.72  thf('75', plain,
% 0.49/0.72      (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.49/0.72         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.49/0.72  thf('76', plain,
% 0.49/0.72      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.49/0.72         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 0.49/0.72      inference('demod', [status(thm)], ['68', '75'])).
% 0.49/0.72  thf('77', plain,
% 0.49/0.72      (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 0.49/0.72         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.49/0.72  thf('78', plain,
% 0.49/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.49/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.72  thf('79', plain,
% 0.49/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.72         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.49/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B))
% 0.49/0.72         = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.72  thf('81', plain,
% 0.49/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.49/0.72  thf(t67_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.49/0.72  thf('82', plain,
% 0.49/0.72      (![X37 : $i, X38 : $i]:
% 0.49/0.72         (((k1_relset_1 @ X37 @ X37 @ X38) = (X37))
% 0.49/0.72          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 0.49/0.72          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 0.49/0.72          | ~ (v1_funct_1 @ X38))),
% 0.49/0.72      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.72        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.49/0.72        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.72  thf('84', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.72  thf('85', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('86', plain,
% 0.49/0.72      (![X24 : $i, X25 : $i]:
% 0.49/0.72         ((v1_funct_2 @ (k2_funct_2 @ X24 @ X25) @ X24 @ X24)
% 0.49/0.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 0.49/0.72          | ~ (v3_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_2 @ X25 @ X24 @ X24)
% 0.49/0.72          | ~ (v1_funct_1 @ X25))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.72  thf('87', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['85', '86'])).
% 0.49/0.72  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('89', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('90', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('91', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.49/0.72  thf('92', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.49/0.72      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.49/0.72  thf('93', plain,
% 0.49/0.72      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['83', '84', '92'])).
% 0.49/0.72  thf('94', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.49/0.72      inference('sup+', [status(thm)], ['80', '93'])).
% 0.49/0.72  thf('95', plain,
% 0.49/0.72      (((k6_relat_1 @ (k2_relat_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['77', '94'])).
% 0.49/0.72  thf('96', plain,
% 0.49/0.72      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['76', '95'])).
% 0.49/0.72  thf('97', plain,
% 0.49/0.72      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.49/0.72         = (k6_relat_1 @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['33', '34', '96'])).
% 0.49/0.72  thf('98', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.49/0.72  thf('99', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72           (k6_partfun1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('100', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.72  thf('101', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72           (k6_relat_1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('demod', [status(thm)], ['99', '100'])).
% 0.49/0.72  thf('102', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72            sk_B) @ 
% 0.49/0.72           (k6_relat_1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['98', '101'])).
% 0.49/0.72  thf('103', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.49/0.72           (k6_relat_1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['97', '102'])).
% 0.49/0.72  thf(dt_k6_partfun1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( m1_subset_1 @
% 0.49/0.72         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.49/0.72       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.49/0.72  thf('104', plain,
% 0.49/0.72      (![X27 : $i]:
% 0.49/0.72         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.49/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.49/0.72  thf('105', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.72  thf('106', plain,
% 0.49/0.72      (![X27 : $i]:
% 0.49/0.72         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.49/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.49/0.72      inference('demod', [status(thm)], ['104', '105'])).
% 0.49/0.72  thf(reflexivity_r2_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.72       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.49/0.72  thf('107', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.72         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.49/0.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.49/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.49/0.72      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.49/0.72  thf('108', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.49/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.49/0.72      inference('condensation', [status(thm)], ['107'])).
% 0.49/0.72  thf('109', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['106', '108'])).
% 0.49/0.72  thf('110', plain,
% 0.49/0.72      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72         (k6_partfun1 @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['103', '109'])).
% 0.49/0.72  thf('111', plain,
% 0.49/0.72      (~
% 0.49/0.72       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72         (k6_partfun1 @ sk_A))) | 
% 0.49/0.72       ~
% 0.49/0.72       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.49/0.72         (k6_partfun1 @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('112', plain,
% 0.49/0.72      (~
% 0.49/0.72       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.49/0.72         (k6_partfun1 @ sk_A)))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['110', '111'])).
% 0.49/0.72  thf('113', plain,
% 0.49/0.72      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.49/0.72          (k6_relat_1 @ sk_A))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['11', '112'])).
% 0.49/0.72  thf('114', plain,
% 0.49/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.49/0.72  thf('115', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('116', plain,
% 0.49/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.49/0.72          | ~ (v1_funct_1 @ X28)
% 0.49/0.72          | ~ (v1_funct_1 @ X31)
% 0.49/0.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.49/0.72          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.49/0.72              = (k5_relat_1 @ X28 @ X31)))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.49/0.72  thf('117', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.49/0.72            = (k5_relat_1 @ sk_B @ X0))
% 0.49/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.72  thf('118', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('119', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.49/0.72            = (k5_relat_1 @ sk_B @ X0))
% 0.49/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.72          | ~ (v1_funct_1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['117', '118'])).
% 0.49/0.72  thf('120', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.72        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.49/0.72            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['114', '119'])).
% 0.49/0.72  thf('121', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.72  thf('122', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.72  thf('123', plain,
% 0.49/0.72      (![X10 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X10)
% 0.49/0.72          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.72  thf('124', plain,
% 0.49/0.72      (![X8 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X8)
% 0.49/0.72          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 0.49/0.72              = (k6_relat_1 @ (k2_relat_1 @ X8)))
% 0.49/0.72          | ~ (v1_funct_1 @ X8)
% 0.49/0.72          | ~ (v1_relat_1 @ X8))),
% 0.49/0.72      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.72  thf('125', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.49/0.72            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_funct_1 @ X0)
% 0.49/0.72          | ~ (v2_funct_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['123', '124'])).
% 0.49/0.72  thf('126', plain,
% 0.49/0.72      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.72        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.72        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.49/0.72            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['122', '125'])).
% 0.49/0.72  thf('127', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.49/0.72  thf('128', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.72  thf('129', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.49/0.72  thf('130', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('131', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.49/0.72  thf('132', plain,
% 0.49/0.72      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.49/0.72         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('demod', [status(thm)],
% 0.49/0.72                ['126', '127', '128', '129', '130', '131'])).
% 0.49/0.72  thf('133', plain,
% 0.49/0.72      (![X8 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X8)
% 0.49/0.72          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.49/0.72              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.49/0.72          | ~ (v1_funct_1 @ X8)
% 0.49/0.72          | ~ (v1_relat_1 @ X8))),
% 0.49/0.72      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.72  thf('134', plain,
% 0.49/0.72      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.49/0.72         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('demod', [status(thm)],
% 0.49/0.72                ['126', '127', '128', '129', '130', '131'])).
% 0.49/0.72  thf('135', plain,
% 0.49/0.72      ((((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.49/0.72          = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v2_funct_1 @ sk_B))),
% 0.49/0.72      inference('sup+', [status(thm)], ['133', '134'])).
% 0.49/0.72  thf('136', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('137', plain,
% 0.49/0.72      (![X37 : $i, X38 : $i]:
% 0.49/0.72         (((k1_relset_1 @ X37 @ X37 @ X38) = (X37))
% 0.49/0.72          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 0.49/0.72          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 0.49/0.72          | ~ (v1_funct_1 @ X38))),
% 0.49/0.72      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.49/0.72  thf('138', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_B)
% 0.49/0.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.49/0.72        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['136', '137'])).
% 0.49/0.72  thf('139', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('140', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('141', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('142', plain,
% 0.49/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.72         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.49/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.72  thf('143', plain,
% 0.49/0.72      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.49/0.72      inference('sup-', [status(thm)], ['141', '142'])).
% 0.49/0.72  thf('144', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['138', '139', '140', '143'])).
% 0.49/0.72  thf('145', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.49/0.72  thf('146', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('147', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.72      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.49/0.72  thf('148', plain,
% 0.49/0.72      (((k6_relat_1 @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.72      inference('demod', [status(thm)], ['135', '144', '145', '146', '147'])).
% 0.49/0.72  thf('149', plain,
% 0.49/0.72      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['132', '148'])).
% 0.49/0.72  thf('150', plain,
% 0.49/0.72      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.49/0.72         = (k6_relat_1 @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['120', '121', '149'])).
% 0.49/0.72  thf('151', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['106', '108'])).
% 0.49/0.72  thf('152', plain, ($false),
% 0.49/0.72      inference('demod', [status(thm)], ['113', '150', '151'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
