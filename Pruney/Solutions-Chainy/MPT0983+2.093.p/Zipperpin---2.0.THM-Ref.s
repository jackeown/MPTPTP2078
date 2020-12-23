%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n3lZ15YbVH

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:15 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 336 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   15
%              Number of atoms          : 1124 (6661 expanded)
%              Number of equality atoms :   44 (  97 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('7',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_relat_1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('22',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['23','26','27','30'])).

thf('32',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('53',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('54',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36 ) )
      | ( v2_funct_1 @ X40 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('64',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','69'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['39','70','72'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('75',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('79',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('83',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('85',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['36','75','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n3lZ15YbVH
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.62  % Solved by: fo/fo7.sh
% 0.35/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.62  % done 272 iterations in 0.165s
% 0.35/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.62  % SZS output start Refutation
% 0.35/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.35/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.35/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.35/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.62  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.35/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.62  thf(t29_funct_2, conjecture,
% 0.35/0.62    (![A:$i,B:$i,C:$i]:
% 0.35/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.62       ( ![D:$i]:
% 0.35/0.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.62           ( ( r2_relset_1 @
% 0.35/0.62               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.62               ( k6_partfun1 @ A ) ) =>
% 0.35/0.62             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.35/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.62          ( ![D:$i]:
% 0.35/0.62            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.62              ( ( r2_relset_1 @
% 0.35/0.62                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.62                  ( k6_partfun1 @ A ) ) =>
% 0.35/0.62                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.35/0.62    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.35/0.62  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.35/0.62      inference('split', [status(esa)], ['0'])).
% 0.35/0.62  thf('2', plain,
% 0.35/0.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.62        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.62        (k6_partfun1 @ sk_A))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(redefinition_k6_partfun1, axiom,
% 0.35/0.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.35/0.62  thf('3', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.35/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.62  thf('4', plain,
% 0.35/0.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.62        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.62        (k6_relat_1 @ sk_A))),
% 0.35/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.62  thf('5', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t24_funct_2, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i]:
% 0.35/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.62       ( ![D:$i]:
% 0.35/0.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.62           ( ( r2_relset_1 @
% 0.35/0.62               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.35/0.62               ( k6_partfun1 @ B ) ) =>
% 0.35/0.62             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.35/0.62  thf('6', plain,
% 0.35/0.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X32)
% 0.35/0.62          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.35/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.35/0.62          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.35/0.62               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.35/0.62               (k6_partfun1 @ X33))
% 0.35/0.62          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.35/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.35/0.62          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.35/0.62          | ~ (v1_funct_1 @ X35))),
% 0.35/0.62      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.35/0.62  thf('7', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.35/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.62  thf('8', plain,
% 0.35/0.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X32)
% 0.35/0.62          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.35/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.35/0.62          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.35/0.62               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.35/0.62               (k6_relat_1 @ X33))
% 0.35/0.62          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.35/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.35/0.62          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.35/0.62          | ~ (v1_funct_1 @ X35))),
% 0.35/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.62  thf('9', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.62          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.35/0.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.62               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.35/0.62               (k6_relat_1 @ sk_A))
% 0.35/0.62          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.62          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.62      inference('sup-', [status(thm)], ['5', '8'])).
% 0.35/0.62  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('12', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.62          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.35/0.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.62               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.35/0.62               (k6_relat_1 @ sk_A)))),
% 0.35/0.62      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.35/0.62  thf('13', plain,
% 0.35/0.62      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.35/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.62        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_D))),
% 0.35/0.62      inference('sup-', [status(thm)], ['4', '12'])).
% 0.35/0.62  thf('14', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i]:
% 0.35/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.62  thf('15', plain,
% 0.35/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.62         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.35/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.35/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.62  thf('16', plain,
% 0.35/0.62      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.35/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.62  thf('17', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('20', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.35/0.62      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 0.35/0.62  thf(d3_funct_2, axiom,
% 0.35/0.62    (![A:$i,B:$i]:
% 0.35/0.62     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.35/0.62       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.35/0.62  thf('21', plain,
% 0.35/0.62      (![X21 : $i, X22 : $i]:
% 0.35/0.62         (((k2_relat_1 @ X22) != (X21))
% 0.35/0.62          | (v2_funct_2 @ X22 @ X21)
% 0.35/0.62          | ~ (v5_relat_1 @ X22 @ X21)
% 0.35/0.62          | ~ (v1_relat_1 @ X22))),
% 0.35/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.35/0.62  thf('22', plain,
% 0.35/0.62      (![X22 : $i]:
% 0.35/0.62         (~ (v1_relat_1 @ X22)
% 0.35/0.62          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 0.35/0.62          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 0.35/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.35/0.62  thf('23', plain,
% 0.35/0.62      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.35/0.62        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.35/0.62        | ~ (v1_relat_1 @ sk_D))),
% 0.35/0.62      inference('sup-', [status(thm)], ['20', '22'])).
% 0.35/0.62  thf('24', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(cc2_relset_1, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i]:
% 0.35/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.62  thf('25', plain,
% 0.35/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.62         ((v5_relat_1 @ X11 @ X13)
% 0.35/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.35/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.62  thf('26', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.35/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.62  thf('27', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.35/0.62      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 0.35/0.62  thf('28', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(cc1_relset_1, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i]:
% 0.35/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.62       ( v1_relat_1 @ C ) ))).
% 0.35/0.62  thf('29', plain,
% 0.35/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.62         ((v1_relat_1 @ X8)
% 0.35/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.35/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.62  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.62  thf('31', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.35/0.62      inference('demod', [status(thm)], ['23', '26', '27', '30'])).
% 0.35/0.62  thf('32', plain,
% 0.35/0.62      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.35/0.62      inference('split', [status(esa)], ['0'])).
% 0.35/0.62  thf('33', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.35/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.62  thf('34', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.35/0.62      inference('split', [status(esa)], ['0'])).
% 0.35/0.62  thf('35', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.35/0.62      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.35/0.62  thf('36', plain, (~ (v2_funct_1 @ sk_C)),
% 0.35/0.62      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 0.35/0.62  thf('37', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t3_subset, axiom,
% 0.35/0.62    (![A:$i,B:$i]:
% 0.35/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.62  thf('38', plain,
% 0.35/0.62      (![X4 : $i, X5 : $i]:
% 0.35/0.62         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.35/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.62  thf('39', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.35/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.62  thf('40', plain,
% 0.35/0.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.62        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.62        (k6_relat_1 @ sk_A))),
% 0.35/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.62  thf('41', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('42', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(dt_k1_partfun1, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.62     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.62         ( v1_funct_1 @ F ) & 
% 0.35/0.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.62       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.35/0.62         ( m1_subset_1 @
% 0.35/0.62           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.35/0.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.35/0.62  thf('43', plain,
% 0.35/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.62         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.35/0.62          | ~ (v1_funct_1 @ X23)
% 0.35/0.62          | ~ (v1_funct_1 @ X26)
% 0.35/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.35/0.62          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.35/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.35/0.62      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.35/0.62  thf('44', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.35/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.35/0.62          | ~ (v1_funct_1 @ X1)
% 0.35/0.62          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.62  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('46', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.35/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.35/0.62          | ~ (v1_funct_1 @ X1))),
% 0.35/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.35/0.62  thf('47', plain,
% 0.35/0.62      ((~ (v1_funct_1 @ sk_D)
% 0.35/0.62        | (m1_subset_1 @ 
% 0.35/0.62           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.35/0.62      inference('sup-', [status(thm)], ['41', '46'])).
% 0.35/0.62  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('49', plain,
% 0.35/0.62      ((m1_subset_1 @ 
% 0.35/0.62        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.35/0.62  thf(redefinition_r2_relset_1, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.62       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.35/0.62  thf('50', plain,
% 0.35/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.35/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.35/0.62          | ((X17) = (X20))
% 0.35/0.62          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.35/0.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.35/0.62  thf('51', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.62             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.35/0.62          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.35/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.62  thf('52', plain,
% 0.35/0.62      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.35/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.62        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.62            = (k6_relat_1 @ sk_A)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['40', '51'])).
% 0.35/0.62  thf(dt_k6_partfun1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( m1_subset_1 @
% 0.35/0.62         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.35/0.62       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.35/0.62  thf('53', plain,
% 0.35/0.62      (![X30 : $i]:
% 0.35/0.62         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.35/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.35/0.62      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.35/0.62  thf('54', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.35/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.62  thf('55', plain,
% 0.35/0.62      (![X30 : $i]:
% 0.35/0.62         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.35/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.35/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.35/0.62  thf('56', plain,
% 0.35/0.62      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.62         = (k6_relat_1 @ sk_A))),
% 0.35/0.62      inference('demod', [status(thm)], ['52', '55'])).
% 0.35/0.62  thf('57', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t26_funct_2, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.62       ( ![E:$i]:
% 0.35/0.62         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.35/0.62             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.35/0.62           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.35/0.62             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.35/0.62               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.35/0.62  thf('58', plain,
% 0.35/0.62      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X36)
% 0.35/0.62          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.35/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.35/0.62          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 0.35/0.62          | (v2_funct_1 @ X40)
% 0.35/0.62          | ((X38) = (k1_xboole_0))
% 0.35/0.62          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.35/0.62          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 0.35/0.62          | ~ (v1_funct_1 @ X40))),
% 0.35/0.62      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.35/0.62  thf('59', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.35/0.62          | ((sk_A) = (k1_xboole_0))
% 0.35/0.62          | (v2_funct_1 @ X0)
% 0.35/0.62          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.35/0.62          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.35/0.62          | ~ (v1_funct_1 @ sk_D))),
% 0.35/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.62  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('62', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.35/0.62          | ((sk_A) = (k1_xboole_0))
% 0.35/0.62          | (v2_funct_1 @ X0)
% 0.35/0.62          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.35/0.62      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.35/0.62  thf('63', plain,
% 0.35/0.62      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.35/0.62        | (v2_funct_1 @ sk_C)
% 0.35/0.62        | ((sk_A) = (k1_xboole_0))
% 0.35/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.35/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.62      inference('sup-', [status(thm)], ['56', '62'])).
% 0.35/0.62  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.35/0.62  thf('64', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.35/0.62      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.35/0.62  thf('65', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('68', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.62      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.35/0.62  thf('69', plain, (~ (v2_funct_1 @ sk_C)),
% 0.35/0.62      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 0.35/0.62  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.62      inference('clc', [status(thm)], ['68', '69'])).
% 0.35/0.62  thf(t113_zfmisc_1, axiom,
% 0.35/0.62    (![A:$i,B:$i]:
% 0.35/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.62  thf('71', plain,
% 0.35/0.62      (![X2 : $i, X3 : $i]:
% 0.35/0.62         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.35/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.62  thf('72', plain,
% 0.35/0.62      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.35/0.62      inference('simplify', [status(thm)], ['71'])).
% 0.35/0.62  thf('73', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.35/0.62      inference('demod', [status(thm)], ['39', '70', '72'])).
% 0.35/0.62  thf(t3_xboole_1, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.62  thf('74', plain,
% 0.35/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.35/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.62  thf('75', plain, (((sk_C) = (k1_xboole_0))),
% 0.35/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.35/0.62  thf('76', plain,
% 0.35/0.62      (![X2 : $i, X3 : $i]:
% 0.35/0.62         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.35/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.62  thf('77', plain,
% 0.35/0.62      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.62      inference('simplify', [status(thm)], ['76'])).
% 0.35/0.62  thf('78', plain,
% 0.35/0.62      (![X30 : $i]:
% 0.35/0.62         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.35/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.35/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.35/0.62  thf('79', plain,
% 0.35/0.62      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.35/0.62      inference('sup+', [status(thm)], ['77', '78'])).
% 0.35/0.62  thf('80', plain,
% 0.35/0.62      (![X4 : $i, X5 : $i]:
% 0.35/0.62         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.35/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.62  thf('81', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.35/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.35/0.62  thf('82', plain,
% 0.35/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.35/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.62  thf('83', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.35/0.62  thf('84', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.35/0.62      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.35/0.62  thf('85', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.35/0.62      inference('sup+', [status(thm)], ['83', '84'])).
% 0.35/0.62  thf('86', plain, ($false),
% 0.35/0.62      inference('demod', [status(thm)], ['36', '75', '85'])).
% 0.35/0.62  
% 0.35/0.62  % SZS output end Refutation
% 0.35/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
