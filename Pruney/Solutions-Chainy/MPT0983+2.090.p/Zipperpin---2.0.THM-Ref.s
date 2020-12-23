%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FqKdJAQxhz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:15 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 341 expanded)
%              Number of leaves         :   41 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          : 1140 (6654 expanded)
%              Number of equality atoms :   35 (  82 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_partfun1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('7',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_relat_1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
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
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != X24 )
      | ( v2_funct_2 @ X25 @ X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('22',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
      | ( v2_funct_2 @ X25 @ ( k2_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('56',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('59',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37 ) )
      | ( v2_funct_1 @ X41 )
      | ( X39 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X38 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('65',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['69','70'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['42','71','72'])).

thf('74',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['37','73'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('75',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('80',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('81',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','86'])).

thf('88',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('89',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['36','76','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FqKdJAQxhz
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 253 iterations in 0.131s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.37/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.37/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.59  thf(t29_funct_2, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.59       ( ![D:$i]:
% 0.37/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.37/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.37/0.59           ( ( r2_relset_1 @
% 0.37/0.59               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.37/0.59               ( k6_partfun1 @ A ) ) =>
% 0.37/0.59             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.59          ( ![D:$i]:
% 0.37/0.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.37/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.37/0.59              ( ( r2_relset_1 @
% 0.37/0.59                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.37/0.59                  ( k6_partfun1 @ A ) ) =>
% 0.37/0.59                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.37/0.59  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.59        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.37/0.59        (k6_partfun1 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k6_partfun1, axiom,
% 0.37/0.59    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.37/0.59  thf('3', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.59        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.37/0.59        (k6_relat_1 @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t24_funct_2, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.59       ( ![D:$i]:
% 0.37/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.37/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.37/0.59           ( ( r2_relset_1 @
% 0.37/0.59               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.37/0.59               ( k6_partfun1 @ B ) ) =>
% 0.37/0.59             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.59         (~ (v1_funct_1 @ X33)
% 0.37/0.59          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.37/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.37/0.59          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 0.37/0.59               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 0.37/0.59               (k6_partfun1 @ X34))
% 0.37/0.59          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.37/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.37/0.59          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.37/0.59          | ~ (v1_funct_1 @ X36))),
% 0.37/0.59      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.37/0.59  thf('7', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.59         (~ (v1_funct_1 @ X33)
% 0.37/0.59          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.37/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.37/0.59          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 0.37/0.59               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 0.37/0.59               (k6_relat_1 @ X34))
% 0.37/0.59          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.37/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.37/0.59          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.37/0.59          | ~ (v1_funct_1 @ X36))),
% 0.37/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_funct_1 @ X0)
% 0.37/0.59          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.37/0.59          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.37/0.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.59               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.37/0.59               (k6_relat_1 @ sk_A))
% 0.37/0.59          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.37/0.59          | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.59  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_funct_1 @ X0)
% 0.37/0.59          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.37/0.59          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.37/0.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.59               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.37/0.59               (k6_relat_1 @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 0.37/0.59        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.37/0.59        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.37/0.59        | ~ (v1_funct_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '12'])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.37/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('20', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 0.37/0.59  thf(d3_funct_2, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.37/0.59       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X24 : $i, X25 : $i]:
% 0.37/0.59         (((k2_relat_1 @ X25) != (X24))
% 0.37/0.59          | (v2_funct_2 @ X25 @ X24)
% 0.37/0.59          | ~ (v5_relat_1 @ X25 @ X24)
% 0.37/0.59          | ~ (v1_relat_1 @ X25))),
% 0.37/0.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      (![X25 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X25)
% 0.37/0.59          | ~ (v5_relat_1 @ X25 @ (k2_relat_1 @ X25))
% 0.37/0.59          | (v2_funct_2 @ X25 @ (k2_relat_1 @ X25)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.37/0.59        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.37/0.59        | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['20', '22'])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(cc2_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.59         ((v5_relat_1 @ X13 @ X15)
% 0.37/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.37/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.59  thf('26', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.37/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.59  thf('27', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(cc1_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( v1_relat_1 @ C ) ))).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.59         ((v1_relat_1 @ X10)
% 0.37/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.37/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.59  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.59  thf('31', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.37/0.59      inference('demod', [status(thm)], ['23', '26', '27', '30'])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('33', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.59  thf('34', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('35', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.37/0.59  thf('36', plain, (~ (v2_funct_1 @ sk_C)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 0.37/0.59  thf(d1_xboole_0, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.59  thf(fc4_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      (![X4 : $i, X5 : $i]:
% 0.37/0.59         (~ (v1_xboole_0 @ X4) | (v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.37/0.59      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t5_subset, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.59          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.59          | ~ (v1_xboole_0 @ X8)
% 0.37/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.37/0.59          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.59  thf('42', plain,
% 0.37/0.59      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['38', '41'])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.59        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.37/0.59        (k6_relat_1 @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('45', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(dt_k1_partfun1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.59         ( v1_funct_1 @ F ) & 
% 0.37/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.37/0.59       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.37/0.59         ( m1_subset_1 @
% 0.37/0.59           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.37/0.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.37/0.59  thf('46', plain,
% 0.37/0.59      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.37/0.59          | ~ (v1_funct_1 @ X26)
% 0.37/0.59          | ~ (v1_funct_1 @ X29)
% 0.37/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.37/0.59          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.37/0.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.37/0.59  thf('47', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.37/0.59          | ~ (v1_funct_1 @ X1)
% 0.37/0.59          | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.59  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.37/0.59          | ~ (v1_funct_1 @ X1))),
% 0.37/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.59  thf('50', plain,
% 0.37/0.59      ((~ (v1_funct_1 @ sk_D)
% 0.37/0.59        | (m1_subset_1 @ 
% 0.37/0.59           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['44', '49'])).
% 0.37/0.59  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('52', plain,
% 0.37/0.59      ((m1_subset_1 @ 
% 0.37/0.59        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.59  thf(redefinition_r2_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.37/0.59  thf('53', plain,
% 0.37/0.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.37/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.37/0.59          | ((X19) = (X22))
% 0.37/0.59          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.37/0.59  thf('54', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.37/0.59             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 0.37/0.59          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.37/0.59        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.37/0.59            = (k6_relat_1 @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['43', '54'])).
% 0.37/0.59  thf(t29_relset_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( m1_subset_1 @
% 0.37/0.59       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.37/0.59  thf('56', plain,
% 0.37/0.59      (![X23 : $i]:
% 0.37/0.59         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.37/0.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.37/0.59  thf('57', plain,
% 0.37/0.59      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.37/0.59         = (k6_relat_1 @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['55', '56'])).
% 0.37/0.59  thf('58', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t26_funct_2, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.59       ( ![E:$i]:
% 0.37/0.59         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.37/0.59             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.37/0.59           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.37/0.59             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.37/0.59               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.37/0.59  thf('59', plain,
% 0.37/0.59      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.37/0.59         (~ (v1_funct_1 @ X37)
% 0.37/0.59          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.37/0.59          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.37/0.59          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 0.37/0.59          | (v2_funct_1 @ X41)
% 0.37/0.59          | ((X39) = (k1_xboole_0))
% 0.37/0.59          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 0.37/0.59          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 0.37/0.59          | ~ (v1_funct_1 @ X41))),
% 0.37/0.59      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.37/0.59  thf('60', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_funct_1 @ X0)
% 0.37/0.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.37/0.59          | ((sk_A) = (k1_xboole_0))
% 0.37/0.59          | (v2_funct_1 @ X0)
% 0.37/0.59          | ~ (v2_funct_1 @ 
% 0.37/0.59               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 0.37/0.59          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.37/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.59  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('63', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_funct_1 @ X0)
% 0.37/0.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.37/0.59          | ((sk_A) = (k1_xboole_0))
% 0.37/0.59          | (v2_funct_1 @ X0)
% 0.37/0.59          | ~ (v2_funct_1 @ 
% 0.37/0.59               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 0.37/0.59      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.37/0.59  thf('64', plain,
% 0.37/0.59      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.37/0.59        | (v2_funct_1 @ sk_C)
% 0.37/0.59        | ((sk_A) = (k1_xboole_0))
% 0.37/0.59        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.37/0.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.37/0.59        | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['57', '63'])).
% 0.37/0.59  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.37/0.59  thf('65', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.37/0.59      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.37/0.59  thf('66', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('69', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.37/0.59  thf('70', plain, (~ (v2_funct_1 @ sk_C)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 0.37/0.59  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.59      inference('clc', [status(thm)], ['69', '70'])).
% 0.37/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.59  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.59  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.37/0.59      inference('demod', [status(thm)], ['42', '71', '72'])).
% 0.37/0.59  thf('74', plain, ((v1_xboole_0 @ sk_C)),
% 0.37/0.59      inference('sup-', [status(thm)], ['37', '73'])).
% 0.37/0.59  thf(l13_xboole_0, axiom,
% 0.37/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.59  thf('75', plain,
% 0.37/0.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.59  thf('76', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.37/0.59  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.59  thf('78', plain,
% 0.37/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.59  thf('79', plain,
% 0.37/0.59      (![X4 : $i, X5 : $i]:
% 0.37/0.59         (~ (v1_xboole_0 @ X4) | (v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.37/0.59      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.37/0.59  thf('80', plain,
% 0.37/0.59      (![X23 : $i]:
% 0.37/0.59         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.37/0.59          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.37/0.59  thf('81', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.59          | ~ (v1_xboole_0 @ X8)
% 0.37/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.59  thf('82', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.37/0.59          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.59  thf('83', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['79', '82'])).
% 0.37/0.59  thf('84', plain,
% 0.37/0.59      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['78', '83'])).
% 0.37/0.59  thf('85', plain,
% 0.37/0.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.59  thf('86', plain,
% 0.37/0.59      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['84', '85'])).
% 0.37/0.59  thf('87', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['77', '86'])).
% 0.37/0.59  thf('88', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.37/0.59      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.37/0.59  thf('89', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.37/0.59      inference('sup+', [status(thm)], ['87', '88'])).
% 0.37/0.59  thf('90', plain, ($false),
% 0.37/0.59      inference('demod', [status(thm)], ['36', '76', '89'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
