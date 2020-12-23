%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7cU64vSPLB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:49 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  270 (5262 expanded)
%              Number of leaves         :   45 (1554 expanded)
%              Depth                    :   25
%              Number of atoms          : 2620 (114010 expanded)
%              Number of equality atoms :  151 (1338 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
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
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relset_1 @ X50 @ X50 @ X51 )
        = X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X50 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != X11 )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf('17',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != X11 )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_C
        = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_C )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C
        = ( k6_partfun1 @ sk_A ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_C )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29','30','31'])).

thf('33',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('39',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('40',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('53',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('63',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('70',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('71',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29 = X32 )
      | ~ ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['60','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('76',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X14 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) )
       != ( k2_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('77',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relset_1 @ X50 @ X50 @ X51 )
        = X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X50 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('92',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['87','88','89','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('96',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','82','83','84','93','94','95'])).

thf('97',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','97'])).

thf('99',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','98'])).

thf('100',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('102',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['80','81'])).

thf('105',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['87','88','89','92'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('109',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_A )
    | ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','107','108'])).

thf('110',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','97'])).

thf('111',plain,
    ( ( sk_A != sk_A )
    | ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','112'])).

thf('114',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf(t66_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X19 @ X18 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['87','88','89','92'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 )
       != ( k2_funct_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['80','81'])).

thf('120',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 )
       != ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
       != ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( sk_A
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['115','122'])).

thf('124',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['80','81'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
       != ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( sk_A
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('130',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('131',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('134',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['129','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','97'])).

thf('147',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['111'])).

thf('149',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('151',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('153',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relset_1 @ X50 @ X50 @ X51 )
        = X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X50 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('154',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('156',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('157',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

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

thf('161',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X48 @ X47 @ X46 )
       != X47 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('162',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('165',plain,(
    ! [X49: $i] :
      ( ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('166',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('171',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('172',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['170','173'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('177',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163','169','177'])).

thf('179',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['111'])).

thf('181',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('183',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('184',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('185',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('186',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('187',plain,(
    ! [X49: $i] :
      ( ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['185','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['184','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['183','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['182','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','97'])).

thf('200',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['111'])).

thf('202',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['154','181','202'])).

thf('204',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['151','203'])).

thf('205',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('206',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('207',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('209',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('211',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['151','203'])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['111'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('215',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','204','209','210','211','212','213','214'])).

thf('216',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','216'])).

thf('218',plain,
    ( sk_C
    = ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 )
      | ( X29 != X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('221',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['219','221'])).

thf('223',plain,(
    $false ),
    inference(demod,[status(thm)],['0','218','222'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7cU64vSPLB
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.06/1.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.30  % Solved by: fo/fo7.sh
% 1.06/1.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.30  % done 1369 iterations in 0.852s
% 1.06/1.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.30  % SZS output start Refutation
% 1.06/1.30  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.06/1.30  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.06/1.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.30  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.30  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.06/1.30  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.30  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.06/1.30  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.06/1.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.30  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.06/1.30  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.30  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.06/1.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.30  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.06/1.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.30  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.06/1.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.30  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.30  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.30  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.06/1.30  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.30  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.06/1.30  thf(t76_funct_2, conjecture,
% 1.06/1.30    (![A:$i,B:$i]:
% 1.06/1.30     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.06/1.30         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.06/1.30       ( ![C:$i]:
% 1.06/1.30         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.06/1.30             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.06/1.30           ( ( ( r2_relset_1 @
% 1.06/1.30                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.06/1.30               ( v2_funct_1 @ B ) ) =>
% 1.06/1.30             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 1.06/1.30  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.30    (~( ![A:$i,B:$i]:
% 1.06/1.30        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.06/1.30            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.06/1.30          ( ![C:$i]:
% 1.06/1.30            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.06/1.30                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.06/1.30              ( ( ( r2_relset_1 @
% 1.06/1.30                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.06/1.30                  ( v2_funct_1 @ B ) ) =>
% 1.06/1.30                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 1.06/1.30    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 1.06/1.30  thf('0', plain,
% 1.06/1.30      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(t61_funct_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ( v2_funct_1 @ A ) =>
% 1.06/1.30         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.06/1.30             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.06/1.30           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.06/1.30             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.06/1.30  thf('1', plain,
% 1.06/1.30      (![X17 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X17)
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.06/1.30              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 1.06/1.30          | ~ (v1_funct_1 @ X17)
% 1.06/1.30          | ~ (v1_relat_1 @ X17))),
% 1.06/1.30      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.06/1.30  thf(redefinition_k6_partfun1, axiom,
% 1.06/1.30    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.06/1.30  thf('2', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.06/1.30  thf('3', plain,
% 1.06/1.30      (![X17 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X17)
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.06/1.30              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.06/1.30          | ~ (v1_funct_1 @ X17)
% 1.06/1.30          | ~ (v1_relat_1 @ X17))),
% 1.06/1.30      inference('demod', [status(thm)], ['1', '2'])).
% 1.06/1.30  thf('4', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(t67_funct_2, axiom,
% 1.06/1.30    (![A:$i,B:$i]:
% 1.06/1.30     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.06/1.30         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.06/1.30       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.06/1.30  thf('5', plain,
% 1.06/1.30      (![X50 : $i, X51 : $i]:
% 1.06/1.30         (((k1_relset_1 @ X50 @ X50 @ X51) = (X50))
% 1.06/1.30          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X50)))
% 1.06/1.30          | ~ (v1_funct_2 @ X51 @ X50 @ X50)
% 1.06/1.30          | ~ (v1_funct_1 @ X51))),
% 1.06/1.30      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.06/1.30  thf('6', plain,
% 1.06/1.30      ((~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.06/1.30        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.30  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('9', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(redefinition_k1_relset_1, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i]:
% 1.06/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.30       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.06/1.30  thf('10', plain,
% 1.06/1.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.30         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.06/1.30          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.06/1.30  thf('11', plain,
% 1.06/1.30      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.30  thf('12', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf(dt_k2_funct_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.06/1.30         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.06/1.30  thf('13', plain,
% 1.06/1.30      (![X9 : $i]:
% 1.06/1.30         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.06/1.30          | ~ (v1_funct_1 @ X9)
% 1.06/1.30          | ~ (v1_relat_1 @ X9))),
% 1.06/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.06/1.30  thf('14', plain,
% 1.06/1.30      (![X9 : $i]:
% 1.06/1.30         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.06/1.30          | ~ (v1_funct_1 @ X9)
% 1.06/1.30          | ~ (v1_relat_1 @ X9))),
% 1.06/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.06/1.30  thf(t55_funct_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ( v2_funct_1 @ A ) =>
% 1.06/1.30         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.06/1.30           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.06/1.30  thf('15', plain,
% 1.06/1.30      (![X16 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X16)
% 1.06/1.30          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 1.06/1.30          | ~ (v1_funct_1 @ X16)
% 1.06/1.30          | ~ (v1_relat_1 @ X16))),
% 1.06/1.30      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.06/1.30  thf(t44_funct_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ![B:$i]:
% 1.06/1.30         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.30           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.06/1.30               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 1.06/1.30             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 1.06/1.30  thf('16', plain,
% 1.06/1.30      (![X10 : $i, X11 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X10)
% 1.06/1.30          | ~ (v1_funct_1 @ X10)
% 1.06/1.30          | ((X10) = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 1.06/1.30          | ((k5_relat_1 @ X11 @ X10) != (X11))
% 1.06/1.30          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 1.06/1.30          | ~ (v1_funct_1 @ X11)
% 1.06/1.30          | ~ (v1_relat_1 @ X11))),
% 1.06/1.30      inference('cnf', [status(esa)], [t44_funct_1])).
% 1.06/1.30  thf('17', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.06/1.30  thf('18', plain,
% 1.06/1.30      (![X10 : $i, X11 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X10)
% 1.06/1.30          | ~ (v1_funct_1 @ X10)
% 1.06/1.30          | ((X10) = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 1.06/1.30          | ((k5_relat_1 @ X11 @ X10) != (X11))
% 1.06/1.30          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 1.06/1.30          | ~ (v1_funct_1 @ X11)
% 1.06/1.30          | ~ (v1_relat_1 @ X11))),
% 1.06/1.30      inference('demod', [status(thm)], ['16', '17'])).
% 1.06/1.30  thf('19', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.06/1.30          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ~ (v1_relat_1 @ X1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['15', '18'])).
% 1.06/1.30  thf('20', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['14', '19'])).
% 1.06/1.30  thf('21', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.06/1.30          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ~ (v1_relat_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0))),
% 1.06/1.30      inference('simplify', [status(thm)], ['20'])).
% 1.06/1.30  thf('22', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['13', '21'])).
% 1.06/1.30  thf('23', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.06/1.30          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ~ (v1_relat_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0))),
% 1.06/1.30      inference('simplify', [status(thm)], ['22'])).
% 1.06/1.30  thf('24', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((k1_relat_1 @ X0) != (sk_A))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ sk_C)
% 1.06/1.30          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30          | ((sk_C) = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ sk_C) != (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0))),
% 1.06/1.30      inference('sup-', [status(thm)], ['12', '23'])).
% 1.06/1.30  thf('25', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(cc2_relat_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( v1_relat_1 @ A ) =>
% 1.06/1.30       ( ![B:$i]:
% 1.06/1.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.06/1.30  thf('26', plain,
% 1.06/1.30      (![X3 : $i, X4 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.06/1.30          | (v1_relat_1 @ X3)
% 1.06/1.30          | ~ (v1_relat_1 @ X4))),
% 1.06/1.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.06/1.30  thf('27', plain,
% 1.06/1.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['25', '26'])).
% 1.06/1.30  thf(fc6_relat_1, axiom,
% 1.06/1.30    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.06/1.30  thf('28', plain,
% 1.06/1.30      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.06/1.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.06/1.30  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('31', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf('32', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((k1_relat_1 @ X0) != (sk_A))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ((sk_C) = (k6_partfun1 @ sk_A))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ sk_C) != (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0))),
% 1.06/1.30      inference('demod', [status(thm)], ['24', '29', '30', '31'])).
% 1.06/1.30  thf('33', plain,
% 1.06/1.30      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.06/1.30        | ((sk_C) = (k6_partfun1 @ sk_A))
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.30        | ((k1_relat_1 @ sk_C) != (sk_A)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['3', '32'])).
% 1.06/1.30  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('38', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf('39', plain,
% 1.06/1.30      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.06/1.30        | ((sk_C) = (k6_partfun1 @ sk_A))
% 1.06/1.30        | ((sk_A) != (sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 1.06/1.30  thf('40', plain,
% 1.06/1.30      ((((sk_C) = (k6_partfun1 @ sk_A))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.06/1.30        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C)))),
% 1.06/1.30      inference('simplify', [status(thm)], ['39'])).
% 1.06/1.30  thf('41', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(cc2_relset_1, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i]:
% 1.06/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.30       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.06/1.30  thf('42', plain,
% 1.06/1.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.30         ((v5_relat_1 @ X20 @ X22)
% 1.06/1.30          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.06/1.30      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.06/1.30  thf('43', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 1.06/1.30      inference('sup-', [status(thm)], ['41', '42'])).
% 1.06/1.30  thf(d19_relat_1, axiom,
% 1.06/1.30    (![A:$i,B:$i]:
% 1.06/1.30     ( ( v1_relat_1 @ B ) =>
% 1.06/1.30       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.06/1.30  thf('44', plain,
% 1.06/1.30      (![X5 : $i, X6 : $i]:
% 1.06/1.30         (~ (v5_relat_1 @ X5 @ X6)
% 1.06/1.30          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 1.06/1.30          | ~ (v1_relat_1 @ X5))),
% 1.06/1.30      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.06/1.30  thf('45', plain,
% 1.06/1.30      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 1.06/1.30      inference('sup-', [status(thm)], ['43', '44'])).
% 1.06/1.30  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 1.06/1.30      inference('demod', [status(thm)], ['45', '46'])).
% 1.06/1.30  thf(d10_xboole_0, axiom,
% 1.06/1.30    (![A:$i,B:$i]:
% 1.06/1.30     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.30  thf('48', plain,
% 1.06/1.30      (![X0 : $i, X2 : $i]:
% 1.06/1.30         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.30  thf('49', plain,
% 1.06/1.30      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))
% 1.06/1.30        | ((sk_A) = (k2_relat_1 @ sk_C)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['47', '48'])).
% 1.06/1.30  thf('50', plain,
% 1.06/1.30      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.06/1.30        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('51', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('52', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(redefinition_k1_partfun1, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.06/1.30     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.30         ( v1_funct_1 @ F ) & 
% 1.06/1.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.06/1.30       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.06/1.30  thf('53', plain,
% 1.06/1.30      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.06/1.30          | ~ (v1_funct_1 @ X39)
% 1.06/1.30          | ~ (v1_funct_1 @ X42)
% 1.06/1.30          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.06/1.30          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 1.06/1.30              = (k5_relat_1 @ X39 @ X42)))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.06/1.30  thf('54', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.30         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.06/1.30            = (k5_relat_1 @ sk_C @ X0))
% 1.06/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['52', '53'])).
% 1.06/1.30  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('56', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.30         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.06/1.30            = (k5_relat_1 @ sk_C @ X0))
% 1.06/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.06/1.30          | ~ (v1_funct_1 @ X0))),
% 1.06/1.30      inference('demod', [status(thm)], ['54', '55'])).
% 1.06/1.30  thf('57', plain,
% 1.06/1.30      ((~ (v1_funct_1 @ sk_B)
% 1.06/1.30        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 1.06/1.30            = (k5_relat_1 @ sk_C @ sk_B)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['51', '56'])).
% 1.06/1.30  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('59', plain,
% 1.06/1.30      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 1.06/1.30         = (k5_relat_1 @ sk_C @ sk_B))),
% 1.06/1.30      inference('demod', [status(thm)], ['57', '58'])).
% 1.06/1.30  thf('60', plain,
% 1.06/1.30      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 1.06/1.30      inference('demod', [status(thm)], ['50', '59'])).
% 1.06/1.30  thf('61', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('62', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(dt_k1_partfun1, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.06/1.30     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.30         ( v1_funct_1 @ F ) & 
% 1.06/1.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.06/1.30       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.06/1.30         ( m1_subset_1 @
% 1.06/1.30           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.06/1.30           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.06/1.30  thf('63', plain,
% 1.06/1.30      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.06/1.30          | ~ (v1_funct_1 @ X33)
% 1.06/1.30          | ~ (v1_funct_1 @ X36)
% 1.06/1.30          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.06/1.30          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 1.06/1.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 1.06/1.30      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.06/1.30  thf('64', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.30         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.06/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.06/1.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['62', '63'])).
% 1.06/1.30  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('66', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.30         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.06/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.06/1.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.06/1.30          | ~ (v1_funct_1 @ X1))),
% 1.06/1.30      inference('demod', [status(thm)], ['64', '65'])).
% 1.06/1.30  thf('67', plain,
% 1.06/1.30      ((~ (v1_funct_1 @ sk_B)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 1.06/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.06/1.30      inference('sup-', [status(thm)], ['61', '66'])).
% 1.06/1.30  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('69', plain,
% 1.06/1.30      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 1.06/1.30         = (k5_relat_1 @ sk_C @ sk_B))),
% 1.06/1.30      inference('demod', [status(thm)], ['57', '58'])).
% 1.06/1.30  thf('70', plain,
% 1.06/1.30      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 1.06/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.06/1.30  thf(redefinition_r2_relset_1, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.30     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.30       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.06/1.30  thf('71', plain,
% 1.06/1.30      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.06/1.30          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.06/1.30          | ((X29) = (X32))
% 1.06/1.30          | ~ (r2_relset_1 @ X30 @ X31 @ X29 @ X32))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.06/1.30  thf('72', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 1.06/1.30          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 1.06/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.06/1.30      inference('sup-', [status(thm)], ['70', '71'])).
% 1.06/1.30  thf('73', plain,
% 1.06/1.30      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.06/1.30        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['60', '72'])).
% 1.06/1.30  thf('74', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('75', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 1.06/1.30      inference('demod', [status(thm)], ['73', '74'])).
% 1.06/1.30  thf(t51_funct_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ![B:$i]:
% 1.06/1.30         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.30           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 1.06/1.30               ( v2_funct_1 @ A ) ) =>
% 1.06/1.30             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.06/1.30  thf('76', plain,
% 1.06/1.30      (![X14 : $i, X15 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X14)
% 1.06/1.30          | ~ (v1_funct_1 @ X14)
% 1.06/1.30          | (r1_tarski @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X14))
% 1.06/1.30          | ((k2_relat_1 @ (k5_relat_1 @ X14 @ X15)) != (k2_relat_1 @ X15))
% 1.06/1.30          | ~ (v2_funct_1 @ X15)
% 1.06/1.30          | ~ (v1_funct_1 @ X15)
% 1.06/1.30          | ~ (v1_relat_1 @ X15))),
% 1.06/1.30      inference('cnf', [status(esa)], [t51_funct_1])).
% 1.06/1.30  thf('77', plain,
% 1.06/1.30      ((((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B))
% 1.06/1.30        | ~ (v1_relat_1 @ sk_B)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_B)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_B)
% 1.06/1.30        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['75', '76'])).
% 1.06/1.30  thf('78', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('79', plain,
% 1.06/1.30      (![X3 : $i, X4 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.06/1.30          | (v1_relat_1 @ X3)
% 1.06/1.30          | ~ (v1_relat_1 @ X4))),
% 1.06/1.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.06/1.30  thf('80', plain,
% 1.06/1.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.06/1.30      inference('sup-', [status(thm)], ['78', '79'])).
% 1.06/1.30  thf('81', plain,
% 1.06/1.30      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.06/1.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.06/1.30  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.30      inference('demod', [status(thm)], ['80', '81'])).
% 1.06/1.30  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('85', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('86', plain,
% 1.06/1.30      (![X50 : $i, X51 : $i]:
% 1.06/1.30         (((k1_relset_1 @ X50 @ X50 @ X51) = (X50))
% 1.06/1.30          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X50)))
% 1.06/1.30          | ~ (v1_funct_2 @ X51 @ X50 @ X50)
% 1.06/1.30          | ~ (v1_funct_1 @ X51))),
% 1.06/1.30      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.06/1.30  thf('87', plain,
% 1.06/1.30      ((~ (v1_funct_1 @ sk_B)
% 1.06/1.30        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.06/1.30        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['85', '86'])).
% 1.06/1.30  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('89', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('90', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('91', plain,
% 1.06/1.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.30         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.06/1.30          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.06/1.30  thf('92', plain,
% 1.06/1.30      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.06/1.30      inference('sup-', [status(thm)], ['90', '91'])).
% 1.06/1.30  thf('93', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['87', '88', '89', '92'])).
% 1.06/1.30  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('96', plain,
% 1.06/1.30      ((((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B))
% 1.06/1.30        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_C)))),
% 1.06/1.30      inference('demod', [status(thm)],
% 1.06/1.30                ['77', '82', '83', '84', '93', '94', '95'])).
% 1.06/1.30  thf('97', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.06/1.30      inference('simplify', [status(thm)], ['96'])).
% 1.06/1.30  thf('98', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['49', '97'])).
% 1.06/1.30  thf('99', plain,
% 1.06/1.30      ((((sk_C) = (k6_partfun1 @ sk_A))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.06/1.30        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C)))),
% 1.06/1.30      inference('demod', [status(thm)], ['40', '98'])).
% 1.06/1.30  thf('100', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 1.06/1.30      inference('demod', [status(thm)], ['73', '74'])).
% 1.06/1.30  thf(t48_funct_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ![B:$i]:
% 1.06/1.30         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.30           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.06/1.30               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.06/1.30             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.06/1.30  thf('101', plain,
% 1.06/1.30      (![X12 : $i, X13 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X12)
% 1.06/1.30          | ~ (v1_funct_1 @ X12)
% 1.06/1.30          | (v2_funct_1 @ X12)
% 1.06/1.30          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 1.06/1.30          | ~ (v2_funct_1 @ (k5_relat_1 @ X12 @ X13))
% 1.06/1.30          | ~ (v1_funct_1 @ X13)
% 1.06/1.30          | ~ (v1_relat_1 @ X13))),
% 1.06/1.30      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.06/1.30  thf('102', plain,
% 1.06/1.30      ((~ (v2_funct_1 @ sk_B)
% 1.06/1.30        | ~ (v1_relat_1 @ sk_B)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_B)
% 1.06/1.30        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_B))
% 1.06/1.30        | (v2_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['100', '101'])).
% 1.06/1.30  thf('103', plain, ((v2_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('104', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.30      inference('demod', [status(thm)], ['80', '81'])).
% 1.06/1.30  thf('105', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('106', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['87', '88', '89', '92'])).
% 1.06/1.30  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('109', plain, ((((k2_relat_1 @ sk_C) != (sk_A)) | (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)],
% 1.06/1.30                ['102', '103', '104', '105', '106', '107', '108'])).
% 1.06/1.30  thf('110', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['49', '97'])).
% 1.06/1.30  thf('111', plain, ((((sk_A) != (sk_A)) | (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['109', '110'])).
% 1.06/1.30  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 1.06/1.30      inference('simplify', [status(thm)], ['111'])).
% 1.06/1.30  thf('113', plain,
% 1.06/1.30      ((((sk_C) = (k6_partfun1 @ sk_A))
% 1.06/1.30        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C)))),
% 1.06/1.30      inference('demod', [status(thm)], ['99', '112'])).
% 1.06/1.30  thf('114', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 1.06/1.30      inference('demod', [status(thm)], ['73', '74'])).
% 1.06/1.30  thf(t66_funct_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ![B:$i]:
% 1.06/1.30         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.06/1.30           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 1.06/1.30             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.06/1.30               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 1.06/1.30  thf('115', plain,
% 1.06/1.30      (![X18 : $i, X19 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X18)
% 1.06/1.30          | ~ (v1_funct_1 @ X18)
% 1.06/1.30          | ((k2_funct_1 @ (k5_relat_1 @ X19 @ X18))
% 1.06/1.30              = (k5_relat_1 @ (k2_funct_1 @ X18) @ (k2_funct_1 @ X19)))
% 1.06/1.30          | ~ (v2_funct_1 @ X18)
% 1.06/1.30          | ~ (v2_funct_1 @ X19)
% 1.06/1.30          | ~ (v1_funct_1 @ X19)
% 1.06/1.30          | ~ (v1_relat_1 @ X19))),
% 1.06/1.30      inference('cnf', [status(esa)], [t66_funct_1])).
% 1.06/1.30  thf('116', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['87', '88', '89', '92'])).
% 1.06/1.30  thf('117', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 1.06/1.30          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ~ (v1_relat_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0))),
% 1.06/1.30      inference('simplify', [status(thm)], ['22'])).
% 1.06/1.30  thf('118', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((sk_A) != (k1_relat_1 @ X0))
% 1.06/1.30          | ~ (v1_relat_1 @ sk_B)
% 1.06/1.30          | ~ (v1_funct_1 @ sk_B)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) != (k2_funct_1 @ sk_B))
% 1.06/1.30          | ~ (v2_funct_1 @ sk_B))),
% 1.06/1.30      inference('sup-', [status(thm)], ['116', '117'])).
% 1.06/1.30  thf('119', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.30      inference('demod', [status(thm)], ['80', '81'])).
% 1.06/1.30  thf('120', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('121', plain, ((v2_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('122', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((sk_A) != (k1_relat_1 @ X0))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.06/1.30          | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) != (k2_funct_1 @ sk_B)))),
% 1.06/1.30      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 1.06/1.30  thf('123', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((k2_funct_1 @ (k5_relat_1 @ X0 @ sk_B)) != (k2_funct_1 @ sk_B))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ sk_B)
% 1.06/1.30          | ~ (v1_funct_1 @ sk_B)
% 1.06/1.30          | ~ (v1_relat_1 @ sk_B)
% 1.06/1.30          | ((k2_funct_1 @ X0)
% 1.06/1.30              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.06/1.30      inference('sup-', [status(thm)], ['115', '122'])).
% 1.06/1.30  thf('124', plain, ((v2_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('125', plain, ((v1_funct_1 @ sk_B)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('126', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.30      inference('demod', [status(thm)], ['80', '81'])).
% 1.06/1.30  thf('127', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((k2_funct_1 @ (k5_relat_1 @ X0 @ sk_B)) != (k2_funct_1 @ sk_B))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ((k2_funct_1 @ X0)
% 1.06/1.30              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.06/1.30      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 1.06/1.30  thf('128', plain,
% 1.06/1.30      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 1.06/1.30        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.06/1.30        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.06/1.30        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.06/1.30        | ((k2_funct_1 @ sk_C)
% 1.06/1.30            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['114', '127'])).
% 1.06/1.30  thf('129', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf('130', plain,
% 1.06/1.30      (![X16 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X16)
% 1.06/1.30          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 1.06/1.30          | ~ (v1_funct_1 @ X16)
% 1.06/1.30          | ~ (v1_relat_1 @ X16))),
% 1.06/1.30      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.06/1.30  thf('131', plain,
% 1.06/1.30      (![X9 : $i]:
% 1.06/1.30         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.06/1.30          | ~ (v1_funct_1 @ X9)
% 1.06/1.30          | ~ (v1_relat_1 @ X9))),
% 1.06/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.06/1.30  thf('132', plain,
% 1.06/1.30      (![X9 : $i]:
% 1.06/1.30         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.06/1.30          | ~ (v1_funct_1 @ X9)
% 1.06/1.30          | ~ (v1_relat_1 @ X9))),
% 1.06/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.06/1.30  thf('133', plain,
% 1.06/1.30      (![X16 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X16)
% 1.06/1.30          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 1.06/1.30          | ~ (v1_funct_1 @ X16)
% 1.06/1.30          | ~ (v1_relat_1 @ X16))),
% 1.06/1.30      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.06/1.30  thf(t3_funct_2, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.30       ( ( v1_funct_1 @ A ) & 
% 1.06/1.30         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.06/1.30         ( m1_subset_1 @
% 1.06/1.30           A @ 
% 1.06/1.30           ( k1_zfmisc_1 @
% 1.06/1.30             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.06/1.30  thf('134', plain,
% 1.06/1.30      (![X49 : $i]:
% 1.06/1.30         ((m1_subset_1 @ X49 @ 
% 1.06/1.30           (k1_zfmisc_1 @ 
% 1.06/1.30            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 1.06/1.30          | ~ (v1_funct_1 @ X49)
% 1.06/1.30          | ~ (v1_relat_1 @ X49))),
% 1.06/1.30      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.06/1.30  thf('135', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30           (k1_zfmisc_1 @ 
% 1.06/1.30            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.06/1.30      inference('sup+', [status(thm)], ['133', '134'])).
% 1.06/1.30  thf('136', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30             (k1_zfmisc_1 @ 
% 1.06/1.30              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.06/1.30               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.06/1.30      inference('sup-', [status(thm)], ['132', '135'])).
% 1.06/1.30  thf('137', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30           (k1_zfmisc_1 @ 
% 1.06/1.30            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0))),
% 1.06/1.30      inference('simplify', [status(thm)], ['136'])).
% 1.06/1.30  thf('138', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30             (k1_zfmisc_1 @ 
% 1.06/1.30              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.06/1.30               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.06/1.30      inference('sup-', [status(thm)], ['131', '137'])).
% 1.06/1.30  thf('139', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30           (k1_zfmisc_1 @ 
% 1.06/1.30            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0))),
% 1.06/1.30      inference('simplify', [status(thm)], ['138'])).
% 1.06/1.30  thf('140', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0))),
% 1.06/1.30      inference('sup+', [status(thm)], ['130', '139'])).
% 1.06/1.30  thf('141', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30             (k1_zfmisc_1 @ 
% 1.06/1.30              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.06/1.30      inference('simplify', [status(thm)], ['140'])).
% 1.06/1.30  thf('142', plain,
% 1.06/1.30      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.06/1.30         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('sup+', [status(thm)], ['129', '141'])).
% 1.06/1.30  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('145', plain,
% 1.06/1.30      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.06/1.30         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['142', '143', '144'])).
% 1.06/1.30  thf('146', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['49', '97'])).
% 1.06/1.30  thf('147', plain,
% 1.06/1.30      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.06/1.30         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['145', '146'])).
% 1.06/1.30  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 1.06/1.30      inference('simplify', [status(thm)], ['111'])).
% 1.06/1.30  thf('149', plain,
% 1.06/1.30      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.06/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['147', '148'])).
% 1.06/1.30  thf('150', plain,
% 1.06/1.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.30         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.06/1.30          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.06/1.30  thf('151', plain,
% 1.06/1.30      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_C))
% 1.06/1.30         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['149', '150'])).
% 1.06/1.30  thf('152', plain,
% 1.06/1.30      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.06/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['147', '148'])).
% 1.06/1.30  thf('153', plain,
% 1.06/1.30      (![X50 : $i, X51 : $i]:
% 1.06/1.30         (((k1_relset_1 @ X50 @ X50 @ X51) = (X50))
% 1.06/1.30          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X50)))
% 1.06/1.30          | ~ (v1_funct_2 @ X51 @ X50 @ X50)
% 1.06/1.30          | ~ (v1_funct_1 @ X51))),
% 1.06/1.30      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.06/1.30  thf('154', plain,
% 1.06/1.30      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.06/1.30        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 1.06/1.30        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['152', '153'])).
% 1.06/1.30  thf('155', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf('156', plain,
% 1.06/1.30      (![X49 : $i]:
% 1.06/1.30         ((m1_subset_1 @ X49 @ 
% 1.06/1.30           (k1_zfmisc_1 @ 
% 1.06/1.30            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 1.06/1.30          | ~ (v1_funct_1 @ X49)
% 1.06/1.30          | ~ (v1_relat_1 @ X49))),
% 1.06/1.30      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.06/1.30  thf('157', plain,
% 1.06/1.30      (((m1_subset_1 @ sk_C @ 
% 1.06/1.30         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C))),
% 1.06/1.30      inference('sup+', [status(thm)], ['155', '156'])).
% 1.06/1.30  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('160', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ 
% 1.06/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 1.06/1.30      inference('demod', [status(thm)], ['157', '158', '159'])).
% 1.06/1.30  thf(t31_funct_2, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i]:
% 1.06/1.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.30       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.06/1.30         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.06/1.30           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.06/1.30           ( m1_subset_1 @
% 1.06/1.30             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.06/1.30  thf('161', plain,
% 1.06/1.30      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X46)
% 1.06/1.30          | ((k2_relset_1 @ X48 @ X47 @ X46) != (X47))
% 1.06/1.30          | (v1_funct_1 @ (k2_funct_1 @ X46))
% 1.06/1.30          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 1.06/1.30          | ~ (v1_funct_2 @ X46 @ X48 @ X47)
% 1.06/1.30          | ~ (v1_funct_1 @ X46))),
% 1.06/1.30      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.06/1.30  thf('162', plain,
% 1.06/1.30      ((~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 1.06/1.30        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.06/1.30        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.06/1.30            != (k2_relat_1 @ sk_C))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['160', '161'])).
% 1.06/1.30  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('164', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf('165', plain,
% 1.06/1.30      (![X49 : $i]:
% 1.06/1.30         ((v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))
% 1.06/1.30          | ~ (v1_funct_1 @ X49)
% 1.06/1.30          | ~ (v1_relat_1 @ X49))),
% 1.06/1.30      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.06/1.30  thf('166', plain,
% 1.06/1.30      (((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C))),
% 1.06/1.30      inference('sup+', [status(thm)], ['164', '165'])).
% 1.06/1.30  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('169', plain, ((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['166', '167', '168'])).
% 1.06/1.30  thf('170', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf('171', plain,
% 1.06/1.30      (![X49 : $i]:
% 1.06/1.30         ((m1_subset_1 @ X49 @ 
% 1.06/1.30           (k1_zfmisc_1 @ 
% 1.06/1.30            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 1.06/1.30          | ~ (v1_funct_1 @ X49)
% 1.06/1.30          | ~ (v1_relat_1 @ X49))),
% 1.06/1.30      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.06/1.30  thf(redefinition_k2_relset_1, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i]:
% 1.06/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.30       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.06/1.30  thf('172', plain,
% 1.06/1.30      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.06/1.30         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.06/1.30          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.06/1.30  thf('173', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.06/1.30              = (k2_relat_1 @ X0)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['171', '172'])).
% 1.06/1.30  thf('174', plain,
% 1.06/1.30      ((((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.06/1.30          = (k2_relat_1 @ sk_C))
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.06/1.30      inference('sup+', [status(thm)], ['170', '173'])).
% 1.06/1.30  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('177', plain,
% 1.06/1.30      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['174', '175', '176'])).
% 1.06/1.30  thf('178', plain,
% 1.06/1.30      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.06/1.30        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['162', '163', '169', '177'])).
% 1.06/1.30  thf('179', plain,
% 1.06/1.30      ((~ (v2_funct_1 @ sk_C) | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.06/1.30      inference('simplify', [status(thm)], ['178'])).
% 1.06/1.30  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 1.06/1.30      inference('simplify', [status(thm)], ['111'])).
% 1.06/1.30  thf('181', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['179', '180'])).
% 1.06/1.30  thf('182', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 1.06/1.30  thf('183', plain,
% 1.06/1.30      (![X16 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X16)
% 1.06/1.30          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 1.06/1.30          | ~ (v1_funct_1 @ X16)
% 1.06/1.30          | ~ (v1_relat_1 @ X16))),
% 1.06/1.30      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.06/1.30  thf('184', plain,
% 1.06/1.30      (![X9 : $i]:
% 1.06/1.30         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.06/1.30          | ~ (v1_funct_1 @ X9)
% 1.06/1.30          | ~ (v1_relat_1 @ X9))),
% 1.06/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.06/1.30  thf('185', plain,
% 1.06/1.30      (![X9 : $i]:
% 1.06/1.30         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.06/1.30          | ~ (v1_funct_1 @ X9)
% 1.06/1.30          | ~ (v1_relat_1 @ X9))),
% 1.06/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.06/1.30  thf('186', plain,
% 1.06/1.30      (![X16 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X16)
% 1.06/1.30          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 1.06/1.30          | ~ (v1_funct_1 @ X16)
% 1.06/1.30          | ~ (v1_relat_1 @ X16))),
% 1.06/1.30      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.06/1.30  thf('187', plain,
% 1.06/1.30      (![X49 : $i]:
% 1.06/1.30         ((v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))
% 1.06/1.30          | ~ (v1_funct_1 @ X49)
% 1.06/1.30          | ~ (v1_relat_1 @ X49))),
% 1.06/1.30      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.06/1.30  thf('188', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.06/1.30           (k1_relat_1 @ X0))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.06/1.30      inference('sup+', [status(thm)], ['186', '187'])).
% 1.06/1.30  thf('189', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['185', '188'])).
% 1.06/1.30  thf('190', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.06/1.30           (k1_relat_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0))),
% 1.06/1.30      inference('simplify', [status(thm)], ['189'])).
% 1.06/1.30  thf('191', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.06/1.30             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['184', '190'])).
% 1.06/1.30  thf('192', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.06/1.30           (k1_relat_1 @ X0))
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0))),
% 1.06/1.30      inference('simplify', [status(thm)], ['191'])).
% 1.06/1.30  thf('193', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.06/1.30           (k1_relat_1 @ X0))
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v2_funct_1 @ X0))),
% 1.06/1.30      inference('sup+', [status(thm)], ['183', '192'])).
% 1.06/1.30  thf('194', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (v2_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_funct_1 @ X0)
% 1.06/1.30          | ~ (v1_relat_1 @ X0)
% 1.06/1.30          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.06/1.30             (k1_relat_1 @ X0)))),
% 1.06/1.30      inference('simplify', [status(thm)], ['193'])).
% 1.06/1.30  thf('195', plain,
% 1.06/1.30      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.06/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('sup+', [status(thm)], ['182', '194'])).
% 1.06/1.30  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('198', plain,
% 1.06/1.30      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['195', '196', '197'])).
% 1.06/1.30  thf('199', plain, (((sk_A) = (k2_relat_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['49', '97'])).
% 1.06/1.30  thf('200', plain,
% 1.06/1.30      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 1.06/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['198', '199'])).
% 1.06/1.30  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 1.06/1.30      inference('simplify', [status(thm)], ['111'])).
% 1.06/1.30  thf('202', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 1.06/1.30      inference('demod', [status(thm)], ['200', '201'])).
% 1.06/1.30  thf('203', plain,
% 1.06/1.30      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['154', '181', '202'])).
% 1.06/1.30  thf('204', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 1.06/1.30      inference('sup+', [status(thm)], ['151', '203'])).
% 1.06/1.30  thf('205', plain,
% 1.06/1.30      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.06/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['147', '148'])).
% 1.06/1.30  thf('206', plain,
% 1.06/1.30      (![X3 : $i, X4 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.06/1.30          | (v1_relat_1 @ X3)
% 1.06/1.30          | ~ (v1_relat_1 @ X4))),
% 1.06/1.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.06/1.30  thf('207', plain,
% 1.06/1.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.06/1.30        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['205', '206'])).
% 1.06/1.30  thf('208', plain,
% 1.06/1.30      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.06/1.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.06/1.30  thf('209', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['207', '208'])).
% 1.06/1.30  thf('210', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.06/1.30      inference('demod', [status(thm)], ['179', '180'])).
% 1.06/1.30  thf('211', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 1.06/1.30      inference('sup+', [status(thm)], ['151', '203'])).
% 1.06/1.30  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 1.06/1.30      inference('simplify', [status(thm)], ['111'])).
% 1.06/1.30  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.30  thf('215', plain,
% 1.06/1.30      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 1.06/1.30        | ((sk_A) != (sk_A))
% 1.06/1.30        | ((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)],
% 1.06/1.30                ['128', '204', '209', '210', '211', '212', '213', '214'])).
% 1.06/1.30  thf('216', plain, (((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['215'])).
% 1.06/1.30  thf('217', plain,
% 1.06/1.30      ((((sk_C) = (k6_partfun1 @ sk_A))
% 1.06/1.30        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['113', '216'])).
% 1.06/1.30  thf('218', plain, (((sk_C) = (k6_partfun1 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['217'])).
% 1.06/1.30  thf('219', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('220', plain,
% 1.06/1.30      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.06/1.30          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.06/1.30          | (r2_relset_1 @ X30 @ X31 @ X29 @ X32)
% 1.06/1.30          | ((X29) != (X32)))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.06/1.30  thf('221', plain,
% 1.06/1.30      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.06/1.30         ((r2_relset_1 @ X30 @ X31 @ X32 @ X32)
% 1.06/1.30          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.06/1.30      inference('simplify', [status(thm)], ['220'])).
% 1.06/1.30  thf('222', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.06/1.30      inference('sup-', [status(thm)], ['219', '221'])).
% 1.06/1.30  thf('223', plain, ($false),
% 1.06/1.30      inference('demod', [status(thm)], ['0', '218', '222'])).
% 1.06/1.30  
% 1.06/1.30  % SZS output end Refutation
% 1.06/1.30  
% 1.06/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
