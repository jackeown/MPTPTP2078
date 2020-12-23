%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qFS6nc2Qkp

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 474 expanded)
%              Number of leaves         :   39 ( 158 expanded)
%              Depth                    :   21
%              Number of atoms          : 1421 (10108 expanded)
%              Number of equality atoms :   52 (  99 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

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
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('14',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_2 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('27',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_2 @ X22 @ X21 )
      | ( ( k2_relat_1 @ X22 )
        = X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['32','35','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['24','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('43',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','40','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['24','39'])).

thf('57',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('58',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('65',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['32','35','38'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('70',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('71',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('72',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('74',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('79',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','75','76','77','78'])).

thf('80',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('81',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['58'])).

thf('91',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','91'])).

thf('93',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('95',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X35 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('100',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('101',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['96','97','98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('104',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('105',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['93','102','103','104','105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qFS6nc2Qkp
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:04:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 96 iterations in 0.061s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.52  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.19/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.52  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.19/0.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.52  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.19/0.52  thf(t61_funct_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.52       ( ( v2_funct_1 @ A ) =>
% 0.19/0.52         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.19/0.52             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.19/0.52           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.19/0.52             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_funct_1 @ X0)
% 0.19/0.52          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.19/0.52              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0)
% 0.19/0.52          | ~ (v1_relat_1 @ X0))),
% 0.19/0.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.19/0.52  thf(redefinition_k6_partfun1, axiom,
% 0.19/0.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.52  thf('1', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_funct_1 @ X0)
% 0.19/0.52          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.19/0.52              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0)
% 0.19/0.52          | ~ (v1_relat_1 @ X0))),
% 0.19/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf(t88_funct_2, conjecture,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.19/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.52       ( ( r2_relset_1 @
% 0.19/0.52           A @ A @ 
% 0.19/0.52           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.19/0.52           ( k6_partfun1 @ A ) ) & 
% 0.19/0.52         ( r2_relset_1 @
% 0.19/0.52           A @ A @ 
% 0.19/0.52           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.19/0.52           ( k6_partfun1 @ A ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i]:
% 0.19/0.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.52            ( v3_funct_2 @ B @ A @ A ) & 
% 0.19/0.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.52          ( ( r2_relset_1 @
% 0.19/0.52              A @ A @ 
% 0.19/0.52              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.19/0.52              ( k6_partfun1 @ A ) ) & 
% 0.19/0.52            ( r2_relset_1 @
% 0.19/0.52              A @ A @ 
% 0.19/0.52              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.19/0.52              ( k6_partfun1 @ A ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.19/0.52           (k6_partfun1 @ sk_A))
% 0.19/0.52        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52             (k6_partfun1 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.19/0.52           (k6_partfun1 @ sk_A)))
% 0.19/0.52         <= (~
% 0.19/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.19/0.52               (k6_partfun1 @ sk_A))))),
% 0.19/0.52      inference('split', [status(esa)], ['3'])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k2_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.19/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.52       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X29 : $i, X30 : $i]:
% 0.19/0.52         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.19/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.19/0.52          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.19/0.52          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.19/0.52          | ~ (v1_funct_1 @ X29))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.19/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.52        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52            (k2_funct_1 @ sk_B)) @ 
% 0.19/0.52           (k6_partfun1 @ sk_A)))
% 0.19/0.52         <= (~
% 0.19/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.19/0.52               (k6_partfun1 @ sk_A))))),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '11'])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_funct_1 @ X0)
% 0.19/0.52          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.19/0.52              = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0)
% 0.19/0.52          | ~ (v1_relat_1 @ X0))),
% 0.19/0.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.19/0.52  thf('14', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_funct_1 @ X0)
% 0.19/0.52          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.19/0.52              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0)
% 0.19/0.52          | ~ (v1_relat_1 @ X0))),
% 0.19/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t31_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.52       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.19/0.52         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.19/0.52           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.19/0.52           ( m1_subset_1 @
% 0.19/0.52             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.52         (~ (v2_funct_1 @ X32)
% 0.19/0.52          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.19/0.52          | (m1_subset_1 @ (k2_funct_1 @ X32) @ 
% 0.19/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.19/0.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.19/0.52          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.19/0.52          | ~ (v1_funct_1 @ X32))),
% 0.19/0.52      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.19/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.52        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.19/0.52        | ~ (v2_funct_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('21', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.52         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.19/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(cc2_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.19/0.52         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.52         (~ (v1_funct_1 @ X18)
% 0.19/0.52          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 0.19/0.52          | (v2_funct_2 @ X18 @ X20)
% 0.19/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (((v2_funct_2 @ sk_B @ sk_A)
% 0.19/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.52  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('30', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.19/0.52  thf(d3_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.19/0.52       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X21 : $i, X22 : $i]:
% 0.19/0.52         (~ (v2_funct_2 @ X22 @ X21)
% 0.19/0.52          | ((k2_relat_1 @ X22) = (X21))
% 0.19/0.52          | ~ (v5_relat_1 @ X22 @ X21)
% 0.19/0.52          | ~ (v1_relat_1 @ X22))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.52        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.19/0.52        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(cc1_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( v1_relat_1 @ C ) ))).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.52         ((v1_relat_1 @ X1)
% 0.19/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.52  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(cc2_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.52         ((v5_relat_1 @ X4 @ X6)
% 0.19/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.52  thf('38', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.19/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.52  thf('39', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['32', '35', '38'])).
% 0.19/0.52  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['24', '39'])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.52         (~ (v1_funct_1 @ X18)
% 0.19/0.52          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 0.19/0.52          | (v2_funct_1 @ X18)
% 0.19/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      (((v2_funct_1 @ sk_B)
% 0.19/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.52  thf('44', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('46', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.52  thf('47', plain,
% 0.19/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.52        | ((sk_A) != (sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['19', '20', '21', '40', '46'])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.52  thf(redefinition_k1_partfun1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.52         ( v1_funct_1 @ F ) & 
% 0.19/0.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.52       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.19/0.52          | ~ (v1_funct_1 @ X23)
% 0.19/0.52          | ~ (v1_funct_1 @ X26)
% 0.19/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.19/0.52          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.19/0.52              = (k5_relat_1 @ X23 @ X26)))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.19/0.52  thf('50', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.19/0.52            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0)
% 0.19/0.52          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.52  thf('51', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('52', plain,
% 0.19/0.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.52         (~ (v2_funct_1 @ X32)
% 0.19/0.52          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.19/0.52          | (v1_funct_1 @ (k2_funct_1 @ X32))
% 0.19/0.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.19/0.52          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.19/0.52          | ~ (v1_funct_1 @ X32))),
% 0.19/0.52      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.19/0.52  thf('53', plain,
% 0.19/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.19/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.52        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.19/0.52        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.19/0.52        | ~ (v2_funct_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.52  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('55', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['24', '39'])).
% 0.19/0.52  thf('57', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.52  thf('58', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_B)) | ((sk_A) != (sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.19/0.52  thf('59', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.19/0.52      inference('simplify', [status(thm)], ['58'])).
% 0.19/0.52  thf('60', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.19/0.52            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0))),
% 0.19/0.52      inference('demod', [status(thm)], ['50', '59'])).
% 0.19/0.52  thf('61', plain,
% 0.19/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.19/0.52        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.52            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['16', '60'])).
% 0.19/0.52  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('63', plain,
% 0.19/0.52      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.19/0.52         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.19/0.52  thf('64', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.19/0.52  thf('65', plain,
% 0.19/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52           (k6_partfun1 @ sk_A)))
% 0.19/0.52         <= (~
% 0.19/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52               (k6_partfun1 @ sk_A))))),
% 0.19/0.52      inference('split', [status(esa)], ['3'])).
% 0.19/0.52  thf('66', plain,
% 0.19/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.52            sk_B) @ 
% 0.19/0.52           (k6_partfun1 @ sk_A)))
% 0.19/0.52         <= (~
% 0.19/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52               (k6_partfun1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.52  thf('67', plain,
% 0.19/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_partfun1 @ sk_A)))
% 0.19/0.52         <= (~
% 0.19/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52               (k6_partfun1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['63', '66'])).
% 0.19/0.52  thf('68', plain,
% 0.19/0.52      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ (k2_relat_1 @ sk_B)) @ 
% 0.19/0.52            (k6_partfun1 @ sk_A))
% 0.19/0.52         | ~ (v1_relat_1 @ sk_B)
% 0.19/0.52         | ~ (v1_funct_1 @ sk_B)
% 0.19/0.52         | ~ (v2_funct_1 @ sk_B)))
% 0.19/0.52         <= (~
% 0.19/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52               (k6_partfun1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['15', '67'])).
% 0.19/0.52  thf('69', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['32', '35', '38'])).
% 0.19/0.52  thf(t29_relset_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( m1_subset_1 @
% 0.19/0.52       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.19/0.52  thf('70', plain,
% 0.19/0.52      (![X17 : $i]:
% 0.19/0.52         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.19/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.19/0.52  thf('71', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.52  thf('72', plain,
% 0.19/0.52      (![X17 : $i]:
% 0.19/0.52         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.19/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.19/0.52      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.52  thf(redefinition_r2_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.19/0.52  thf('73', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.19/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.19/0.52          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 0.19/0.52          | ((X13) != (X16)))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.19/0.52  thf('74', plain,
% 0.19/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.52         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.19/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.19/0.52      inference('simplify', [status(thm)], ['73'])).
% 0.19/0.52  thf('75', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['72', '74'])).
% 0.19/0.52  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('78', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.52  thf('79', plain,
% 0.19/0.52      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52         (k6_partfun1 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['68', '69', '75', '76', '77', '78'])).
% 0.19/0.52  thf('80', plain,
% 0.19/0.52      (~
% 0.19/0.52       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.19/0.52         (k6_partfun1 @ sk_A))) | 
% 0.19/0.52       ~
% 0.19/0.52       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.19/0.52          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.19/0.52         (k6_partfun1 @ sk_A)))),
% 0.19/0.52      inference('split', [status(esa)], ['3'])).
% 0.19/0.52  thf('81', plain,
% 0.19/0.52      (~
% 0.19/0.52       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.19/0.52         (k6_partfun1 @ sk_A)))),
% 0.19/0.52      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 0.19/0.52  thf('82', plain,
% 0.19/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.19/0.52          (k6_partfun1 @ sk_A))),
% 0.19/0.52      inference('simpl_trail', [status(thm)], ['12', '81'])).
% 0.19/0.52  thf('83', plain,
% 0.19/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.52  thf('84', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('85', plain,
% 0.19/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.19/0.52          | ~ (v1_funct_1 @ X23)
% 0.19/0.52          | ~ (v1_funct_1 @ X26)
% 0.19/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.19/0.52          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.19/0.52              = (k5_relat_1 @ X23 @ X26)))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.19/0.52  thf('86', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.19/0.52            = (k5_relat_1 @ sk_B @ X0))
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0)
% 0.19/0.52          | ~ (v1_funct_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['84', '85'])).
% 0.19/0.52  thf('87', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('88', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.19/0.52            = (k5_relat_1 @ sk_B @ X0))
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.52          | ~ (v1_funct_1 @ X0))),
% 0.19/0.52      inference('demod', [status(thm)], ['86', '87'])).
% 0.19/0.52  thf('89', plain,
% 0.19/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.19/0.52        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.52            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['83', '88'])).
% 0.19/0.52  thf('90', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.19/0.52      inference('simplify', [status(thm)], ['58'])).
% 0.19/0.52  thf('91', plain,
% 0.19/0.52      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.19/0.52         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.19/0.52      inference('demod', [status(thm)], ['89', '90'])).
% 0.19/0.52  thf('92', plain,
% 0.19/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_partfun1 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['82', '91'])).
% 0.19/0.52  thf('93', plain,
% 0.19/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ (k1_relat_1 @ sk_B)) @ 
% 0.19/0.52           (k6_partfun1 @ sk_A))
% 0.19/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.19/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.52        | ~ (v2_funct_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '92'])).
% 0.19/0.52  thf('94', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t67_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.52       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.19/0.52  thf('95', plain,
% 0.19/0.52      (![X35 : $i, X36 : $i]:
% 0.19/0.52         (((k1_relset_1 @ X35 @ X35 @ X36) = (X35))
% 0.19/0.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.19/0.52          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.19/0.52          | ~ (v1_funct_1 @ X36))),
% 0.19/0.52      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.19/0.52  thf('96', plain,
% 0.19/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.19/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.52        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.52  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('98', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('99', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.52  thf('100', plain,
% 0.19/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.52         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.19/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.52  thf('101', plain,
% 0.19/0.52      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['99', '100'])).
% 0.19/0.52  thf('102', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['96', '97', '98', '101'])).
% 0.19/0.52  thf('103', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['72', '74'])).
% 0.19/0.52  thf('104', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('105', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('106', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.52  thf('107', plain, ($false),
% 0.19/0.52      inference('demod', [status(thm)],
% 0.19/0.52                ['93', '102', '103', '104', '105', '106'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
