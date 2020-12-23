%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dY6ebnsxOT

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:46 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 259 expanded)
%              Number of leaves         :   39 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          : 1299 (5355 expanded)
%              Number of equality atoms :   76 ( 173 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(t75_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
              & ( ( k2_relset_1 @ A @ A @ B )
                = A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
                & ( ( k2_relset_1 @ A @ A @ B )
                  = A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relset_1 @ X52 @ X52 @ X53 )
        = X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X52 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['8','9','10','13'])).

thf(t44_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k5_relat_1 @ X12 @ X11 )
       != X12 )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k5_relat_1 @ X12 @ X11 )
       != X12 )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != X0 )
      | ( sk_C
        = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['8','9','10','13'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != X0 )
      | ( sk_C
        = ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','23'])).

thf('25',plain,
    ( ( sk_A != sk_A )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A != sk_A )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
     != sk_B ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,
    ( ( ( k5_relat_1 @ sk_B @ sk_C )
     != sk_B )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X8: $i] :
      ( ( ( k10_relat_1 @ X8 @ ( k2_relat_1 @ X8 ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('47',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relset_1 @ X52 @ X52 @ X53 )
        = X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X52 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('57',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['47','56'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )).

thf('60',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ X48 @ X49 @ X50 @ X51 ) @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('65',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','66'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k9_relat_1 @ X6 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('72',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X36 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['8','9','10','13'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X0 @ sk_A ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X0 @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X0 @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k10_relat_1 @ X0 @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('87',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('88',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['42','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','92'])).

thf('94',plain,
    ( sk_C
    = ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('97',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dY6ebnsxOT
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.84  % Solved by: fo/fo7.sh
% 0.66/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.84  % done 596 iterations in 0.358s
% 0.66/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.84  % SZS output start Refutation
% 0.66/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.84  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.66/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.66/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.66/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.84  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.66/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.66/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.84  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.66/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.84  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.66/0.84  thf(t75_funct_2, conjecture,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.84       ( ![C:$i]:
% 0.66/0.84         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.66/0.84             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.84           ( ( ( r2_relset_1 @
% 0.66/0.84                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.66/0.84               ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.66/0.84             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.66/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.84    (~( ![A:$i,B:$i]:
% 0.66/0.84        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.84            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.84          ( ![C:$i]:
% 0.66/0.84            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.66/0.84                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.84              ( ( ( r2_relset_1 @
% 0.66/0.84                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.66/0.84                  ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.66/0.84                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.66/0.84    inference('cnf.neg', [status(esa)], [t75_funct_2])).
% 0.66/0.84  thf('0', plain,
% 0.66/0.84      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('1', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(redefinition_k2_relset_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.66/0.84  thf('2', plain,
% 0.66/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.84         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.66/0.84          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.66/0.84  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.66/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.84  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('5', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.66/0.84      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.84  thf('6', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(t67_funct_2, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.84       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.66/0.84  thf('7', plain,
% 0.66/0.84      (![X52 : $i, X53 : $i]:
% 0.66/0.84         (((k1_relset_1 @ X52 @ X52 @ X53) = (X52))
% 0.66/0.84          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X52)))
% 0.66/0.84          | ~ (v1_funct_2 @ X53 @ X52 @ X52)
% 0.66/0.84          | ~ (v1_funct_1 @ X53))),
% 0.66/0.84      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.66/0.84  thf('8', plain,
% 0.66/0.84      ((~ (v1_funct_1 @ sk_C)
% 0.66/0.84        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.66/0.84        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.66/0.84  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('11', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.66/0.84  thf('12', plain,
% 0.66/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.84         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.66/0.84          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.84  thf('13', plain,
% 0.66/0.84      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.66/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.84  thf('14', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['8', '9', '10', '13'])).
% 0.66/0.84  thf(t44_funct_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.84       ( ![B:$i]:
% 0.66/0.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.84           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.66/0.84               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.66/0.84             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.66/0.84  thf('15', plain,
% 0.66/0.84      (![X11 : $i, X12 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X11)
% 0.66/0.84          | ~ (v1_funct_1 @ X11)
% 0.66/0.84          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.66/0.84          | ((k5_relat_1 @ X12 @ X11) != (X12))
% 0.66/0.84          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.66/0.84          | ~ (v1_funct_1 @ X12)
% 0.66/0.84          | ~ (v1_relat_1 @ X12))),
% 0.66/0.84      inference('cnf', [status(esa)], [t44_funct_1])).
% 0.66/0.84  thf(redefinition_k6_partfun1, axiom,
% 0.66/0.84    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.66/0.84  thf('16', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.84  thf('17', plain,
% 0.66/0.84      (![X11 : $i, X12 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X11)
% 0.66/0.84          | ~ (v1_funct_1 @ X11)
% 0.66/0.84          | ((X11) = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.66/0.84          | ((k5_relat_1 @ X12 @ X11) != (X12))
% 0.66/0.84          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.66/0.84          | ~ (v1_funct_1 @ X12)
% 0.66/0.84          | ~ (v1_relat_1 @ X12))),
% 0.66/0.84      inference('demod', [status(thm)], ['15', '16'])).
% 0.66/0.84  thf('18', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (((k2_relat_1 @ X0) != (sk_A))
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_funct_1 @ X0)
% 0.66/0.84          | ((k5_relat_1 @ X0 @ sk_C) != (X0))
% 0.66/0.84          | ((sk_C) = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.66/0.84          | ~ (v1_funct_1 @ sk_C)
% 0.66/0.84          | ~ (v1_relat_1 @ sk_C))),
% 0.66/0.84      inference('sup-', [status(thm)], ['14', '17'])).
% 0.66/0.84  thf('19', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['8', '9', '10', '13'])).
% 0.66/0.84  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('21', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(cc1_relset_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.84       ( v1_relat_1 @ C ) ))).
% 0.66/0.84  thf('22', plain,
% 0.66/0.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.66/0.84         ((v1_relat_1 @ X13)
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.66/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.66/0.84  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.84      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.84  thf('24', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (((k2_relat_1 @ X0) != (sk_A))
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_funct_1 @ X0)
% 0.66/0.84          | ((k5_relat_1 @ X0 @ sk_C) != (X0))
% 0.66/0.84          | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 0.66/0.84      inference('demod', [status(thm)], ['18', '19', '20', '23'])).
% 0.66/0.84  thf('25', plain,
% 0.66/0.84      ((((sk_A) != (sk_A))
% 0.66/0.84        | ((sk_C) = (k6_partfun1 @ sk_A))
% 0.66/0.84        | ((k5_relat_1 @ sk_B @ sk_C) != (sk_B))
% 0.66/0.84        | ~ (v1_funct_1 @ sk_B)
% 0.66/0.84        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.84      inference('sup-', [status(thm)], ['5', '24'])).
% 0.66/0.84  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('27', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('28', plain,
% 0.66/0.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.66/0.84         ((v1_relat_1 @ X13)
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.66/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.66/0.84  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('30', plain,
% 0.66/0.84      ((((sk_A) != (sk_A))
% 0.66/0.84        | ((sk_C) = (k6_partfun1 @ sk_A))
% 0.66/0.84        | ((k5_relat_1 @ sk_B @ sk_C) != (sk_B)))),
% 0.66/0.84      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.66/0.84  thf('31', plain,
% 0.66/0.84      ((((k5_relat_1 @ sk_B @ sk_C) != (sk_B))
% 0.66/0.84        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['30'])).
% 0.66/0.84  thf('32', plain,
% 0.66/0.84      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.84        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('33', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('34', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(redefinition_k1_partfun1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.84     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.84         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.84         ( v1_funct_1 @ F ) & 
% 0.66/0.84         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.84       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.66/0.84  thf('35', plain,
% 0.66/0.84      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.66/0.84          | ~ (v1_funct_1 @ X41)
% 0.66/0.84          | ~ (v1_funct_1 @ X44)
% 0.66/0.84          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.66/0.84          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 0.66/0.84              = (k5_relat_1 @ X41 @ X44)))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.66/0.84  thf('36', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.66/0.84            = (k5_relat_1 @ sk_B @ X0))
% 0.66/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.84          | ~ (v1_funct_1 @ X0)
% 0.66/0.84          | ~ (v1_funct_1 @ sk_B))),
% 0.66/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.66/0.84  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('38', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.66/0.84            = (k5_relat_1 @ sk_B @ X0))
% 0.66/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.84          | ~ (v1_funct_1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.84  thf('39', plain,
% 0.66/0.84      ((~ (v1_funct_1 @ sk_C)
% 0.66/0.84        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.66/0.84            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['33', '38'])).
% 0.66/0.84  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('41', plain,
% 0.66/0.84      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.66/0.84         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.66/0.84      inference('demod', [status(thm)], ['39', '40'])).
% 0.66/0.84  thf('42', plain,
% 0.66/0.84      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ sk_B)),
% 0.66/0.84      inference('demod', [status(thm)], ['32', '41'])).
% 0.66/0.84  thf('43', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.66/0.84      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.84  thf(t169_relat_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ A ) =>
% 0.66/0.84       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.66/0.84  thf('44', plain,
% 0.66/0.84      (![X8 : $i]:
% 0.66/0.84         (((k10_relat_1 @ X8 @ (k2_relat_1 @ X8)) = (k1_relat_1 @ X8))
% 0.66/0.84          | ~ (v1_relat_1 @ X8))),
% 0.66/0.84      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.66/0.84  thf('45', plain,
% 0.66/0.84      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_relat_1 @ sk_B))
% 0.66/0.84        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.84      inference('sup+', [status(thm)], ['43', '44'])).
% 0.66/0.84  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('47', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.66/0.84      inference('demod', [status(thm)], ['45', '46'])).
% 0.66/0.84  thf('48', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('49', plain,
% 0.66/0.84      (![X52 : $i, X53 : $i]:
% 0.66/0.84         (((k1_relset_1 @ X52 @ X52 @ X53) = (X52))
% 0.66/0.84          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X52)))
% 0.66/0.84          | ~ (v1_funct_2 @ X53 @ X52 @ X52)
% 0.66/0.84          | ~ (v1_funct_1 @ X53))),
% 0.66/0.84      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.66/0.84  thf('50', plain,
% 0.66/0.84      ((~ (v1_funct_1 @ sk_B)
% 0.66/0.84        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.84        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['48', '49'])).
% 0.66/0.84  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('52', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('53', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('54', plain,
% 0.66/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.84         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.66/0.84          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.84  thf('55', plain,
% 0.66/0.84      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.66/0.84      inference('sup-', [status(thm)], ['53', '54'])).
% 0.66/0.84  thf('56', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 0.66/0.84  thf('57', plain, (((k10_relat_1 @ sk_B @ sk_A) = (sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['47', '56'])).
% 0.66/0.84  thf(dt_k5_relat_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.66/0.84       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.66/0.84  thf('58', plain,
% 0.66/0.84      (![X3 : $i, X4 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X3)
% 0.66/0.84          | ~ (v1_relat_1 @ X4)
% 0.66/0.84          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.66/0.84      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.66/0.84  thf('59', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(t44_funct_2, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.66/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.84       ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ))).
% 0.66/0.84  thf('60', plain,
% 0.66/0.84      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.66/0.84         ((r1_tarski @ (k7_relset_1 @ X48 @ X49 @ X50 @ X51) @ X49)
% 0.66/0.84          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.66/0.84          | ~ (v1_funct_2 @ X50 @ X48 @ X49)
% 0.66/0.84          | ~ (v1_funct_1 @ X50))),
% 0.66/0.84      inference('cnf', [status(esa)], [t44_funct_2])).
% 0.66/0.84  thf('61', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v1_funct_1 @ sk_C)
% 0.66/0.84          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.66/0.84          | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) @ sk_A))),
% 0.66/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.66/0.84  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('64', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(redefinition_k7_relset_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.84       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.66/0.84  thf('65', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.66/0.84          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.66/0.84  thf('66', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['64', '65'])).
% 0.66/0.84  thf('67', plain, (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ sk_A)),
% 0.66/0.84      inference('demod', [status(thm)], ['61', '62', '63', '66'])).
% 0.66/0.84  thf(t160_relat_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ A ) =>
% 0.66/0.84       ( ![B:$i]:
% 0.66/0.84         ( ( v1_relat_1 @ B ) =>
% 0.66/0.84           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.66/0.84             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.66/0.84  thf('68', plain,
% 0.66/0.84      (![X6 : $i, X7 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X6)
% 0.66/0.84          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.66/0.84              = (k9_relat_1 @ X6 @ (k2_relat_1 @ X7)))
% 0.66/0.84          | ~ (v1_relat_1 @ X7))),
% 0.66/0.84      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.66/0.84  thf(d10_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.84  thf('69', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.66/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.84  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.66/0.84      inference('simplify', [status(thm)], ['69'])).
% 0.66/0.84  thf(t182_relat_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ A ) =>
% 0.66/0.84       ( ![B:$i]:
% 0.66/0.84         ( ( v1_relat_1 @ B ) =>
% 0.66/0.84           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.66/0.84             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.66/0.84  thf('71', plain,
% 0.66/0.84      (![X9 : $i, X10 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X9)
% 0.66/0.84          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 0.66/0.84              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 0.66/0.84          | ~ (v1_relat_1 @ X10))),
% 0.66/0.84      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.66/0.84  thf(t11_relset_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ C ) =>
% 0.66/0.84       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.66/0.84           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.66/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.66/0.84  thf('72', plain,
% 0.66/0.84      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.66/0.84         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 0.66/0.84          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ X36)
% 0.66/0.84          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.66/0.84          | ~ (v1_relat_1 @ X34))),
% 0.66/0.84      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.66/0.84  thf('73', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 0.66/0.84          | ~ (v1_relat_1 @ X1)
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.66/0.84          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.66/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3)))
% 0.66/0.84          | ~ (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ X3))),
% 0.66/0.84      inference('sup-', [status(thm)], ['71', '72'])).
% 0.66/0.84  thf('74', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 0.66/0.84          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.66/0.84             (k1_zfmisc_1 @ 
% 0.66/0.84              (k2_zfmisc_1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)))
% 0.66/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_relat_1 @ X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['70', '73'])).
% 0.66/0.84  thf('75', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r1_tarski @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ X2)
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_relat_1 @ X1)
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_relat_1 @ X1)
% 0.66/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.66/0.84          | (m1_subset_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.66/0.84             (k1_zfmisc_1 @ 
% 0.66/0.84              (k2_zfmisc_1 @ (k10_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ X2))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['68', '74'])).
% 0.66/0.84  thf('76', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((m1_subset_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.66/0.84           (k1_zfmisc_1 @ 
% 0.66/0.84            (k2_zfmisc_1 @ (k10_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ X2)))
% 0.66/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.66/0.84          | ~ (v1_relat_1 @ X1)
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ X2))),
% 0.66/0.84      inference('simplify', [status(thm)], ['75'])).
% 0.66/0.84  thf('77', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_relat_1 @ sk_C)
% 0.66/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_C))
% 0.66/0.84          | (m1_subset_1 @ (k5_relat_1 @ X0 @ sk_C) @ 
% 0.66/0.84             (k1_zfmisc_1 @ 
% 0.66/0.84              (k2_zfmisc_1 @ (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_C)) @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['67', '76'])).
% 0.66/0.84  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.84      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.84  thf('79', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['8', '9', '10', '13'])).
% 0.66/0.84  thf('80', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X0)
% 0.66/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_C))
% 0.66/0.84          | (m1_subset_1 @ (k5_relat_1 @ X0 @ sk_C) @ 
% 0.66/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k10_relat_1 @ X0 @ sk_A) @ sk_A))))),
% 0.66/0.84      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.66/0.84  thf('81', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ sk_C)
% 0.66/0.84          | ~ (v1_relat_1 @ X0)
% 0.66/0.84          | (m1_subset_1 @ (k5_relat_1 @ X0 @ sk_C) @ 
% 0.66/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k10_relat_1 @ X0 @ sk_A) @ sk_A)))
% 0.66/0.84          | ~ (v1_relat_1 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['58', '80'])).
% 0.66/0.84  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.84      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.84  thf('83', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X0)
% 0.66/0.84          | (m1_subset_1 @ (k5_relat_1 @ X0 @ sk_C) @ 
% 0.66/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k10_relat_1 @ X0 @ sk_A) @ sk_A)))
% 0.66/0.84          | ~ (v1_relat_1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['81', '82'])).
% 0.66/0.84  thf('84', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((m1_subset_1 @ (k5_relat_1 @ X0 @ sk_C) @ 
% 0.66/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k10_relat_1 @ X0 @ sk_A) @ sk_A)))
% 0.66/0.84          | ~ (v1_relat_1 @ X0))),
% 0.66/0.84      inference('simplify', [status(thm)], ['83'])).
% 0.66/0.84  thf('85', plain,
% 0.66/0.84      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 0.66/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.66/0.84        | ~ (v1_relat_1 @ sk_B))),
% 0.66/0.84      inference('sup+', [status(thm)], ['57', '84'])).
% 0.66/0.84  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('87', plain,
% 0.66/0.84      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 0.66/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('demod', [status(thm)], ['85', '86'])).
% 0.66/0.84  thf(redefinition_r2_relset_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.84     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.84       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.66/0.84  thf('88', plain,
% 0.66/0.84      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.66/0.84          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.66/0.84          | ((X26) = (X29))
% 0.66/0.84          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.66/0.84  thf('89', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ X0)
% 0.66/0.84          | ((k5_relat_1 @ sk_B @ sk_C) = (X0))
% 0.66/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['87', '88'])).
% 0.66/0.84  thf('90', plain,
% 0.66/0.84      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.66/0.84        | ((k5_relat_1 @ sk_B @ sk_C) = (sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['42', '89'])).
% 0.66/0.84  thf('91', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('92', plain, (((k5_relat_1 @ sk_B @ sk_C) = (sk_B))),
% 0.66/0.84      inference('demod', [status(thm)], ['90', '91'])).
% 0.66/0.84  thf('93', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 0.66/0.84      inference('demod', [status(thm)], ['31', '92'])).
% 0.66/0.84  thf('94', plain, (((sk_C) = (k6_partfun1 @ sk_A))),
% 0.66/0.84      inference('simplify', [status(thm)], ['93'])).
% 0.66/0.84  thf('95', plain,
% 0.66/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('96', plain,
% 0.66/0.84      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.66/0.84          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.66/0.84          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 0.66/0.84          | ((X26) != (X29)))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.66/0.84  thf('97', plain,
% 0.66/0.84      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.84         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 0.66/0.84          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.66/0.84      inference('simplify', [status(thm)], ['96'])).
% 0.66/0.84  thf('98', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.66/0.84      inference('sup-', [status(thm)], ['95', '97'])).
% 0.66/0.84  thf('99', plain, ($false),
% 0.66/0.84      inference('demod', [status(thm)], ['0', '94', '98'])).
% 0.66/0.84  
% 0.66/0.84  % SZS output end Refutation
% 0.66/0.84  
% 0.66/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
