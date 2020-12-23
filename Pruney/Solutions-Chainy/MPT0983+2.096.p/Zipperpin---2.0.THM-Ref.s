%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0qIhZMF1p0

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 309 expanded)
%              Number of leaves         :   42 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          : 1067 (6324 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('3',plain,(
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

thf('4',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ X29 )
       != X28 )
      | ( v2_funct_2 @ X29 @ X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X29: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
      | ( v2_funct_2 @ X29 @ ( k2_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['19','22','23','26'])).

thf('28',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('33',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('50',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('51',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X44 @ X42 @ X42 @ X43 @ X45 @ X41 ) )
      | ( v2_funct_1 @ X45 )
      | ( X43 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X42 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('62',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','63','64','65','66'])).

thf('68',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['67','68'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('71',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['36','69','71','72'])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','73'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('75',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('76',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('79',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['32','74','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0qIhZMF1p0
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 250 iterations in 0.174s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.45/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(t29_funct_2, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ![D:$i]:
% 0.45/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.45/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.45/0.64           ( ( r2_relset_1 @
% 0.45/0.64               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.45/0.64               ( k6_partfun1 @ A ) ) =>
% 0.45/0.64             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64          ( ![D:$i]:
% 0.45/0.64            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.45/0.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.45/0.64              ( ( r2_relset_1 @
% 0.45/0.64                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.45/0.64                  ( k6_partfun1 @ A ) ) =>
% 0.45/0.64                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.45/0.64  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.64        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.64        (k6_partfun1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t24_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ![D:$i]:
% 0.45/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.45/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.45/0.64           ( ( r2_relset_1 @
% 0.45/0.64               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.45/0.64               ( k6_partfun1 @ B ) ) =>
% 0.45/0.64             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.64         (~ (v1_funct_1 @ X37)
% 0.45/0.64          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.45/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.64          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 0.45/0.64               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 0.45/0.64               (k6_partfun1 @ X38))
% 0.45/0.64          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 0.45/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.45/0.64          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.45/0.64          | ~ (v1_funct_1 @ X40))),
% 0.45/0.64      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.45/0.64          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.45/0.64          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.64               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.45/0.64               (k6_partfun1 @ sk_A))
% 0.45/0.64          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.45/0.64          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.45/0.64          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.64               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.45/0.64               (k6_partfun1 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 0.45/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.45/0.64        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '8'])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.45/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.45/0.64  thf(d3_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X28 : $i, X29 : $i]:
% 0.45/0.64         (((k2_relat_1 @ X29) != (X28))
% 0.45/0.64          | (v2_funct_2 @ X29 @ X28)
% 0.45/0.64          | ~ (v5_relat_1 @ X29 @ X28)
% 0.45/0.64          | ~ (v1_relat_1 @ X29))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X29 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X29)
% 0.45/0.64          | ~ (v5_relat_1 @ X29 @ (k2_relat_1 @ X29))
% 0.45/0.64          | (v2_funct_2 @ X29 @ (k2_relat_1 @ X29)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.45/0.64        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '18'])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.64         ((v5_relat_1 @ X11 @ X13)
% 0.45/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('22', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.45/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X8)
% 0.45/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '22', '23', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('29', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.64  thf('30', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('31', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain, (~ (v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.45/0.64  thf(t6_mcart_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.64                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.64                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.45/0.64                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.45/0.64                       ( r2_hidden @ G @ B ) ) =>
% 0.45/0.64                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X22 : $i]:
% 0.45/0.64         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.45/0.64      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t5_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.64          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X3 @ X4)
% 0.45/0.64          | ~ (v1_xboole_0 @ X5)
% 0.45/0.64          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.45/0.64          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.64        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.64        (k6_partfun1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_k1_partfun1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.64         ( v1_funct_1 @ F ) & 
% 0.45/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.64       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.45/0.64         ( m1_subset_1 @
% 0.45/0.64           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.45/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.45/0.64          | ~ (v1_funct_1 @ X30)
% 0.45/0.64          | ~ (v1_funct_1 @ X33)
% 0.45/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.45/0.64          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.64  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1))),
% 0.45/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_D)
% 0.45/0.64        | (m1_subset_1 @ 
% 0.45/0.64           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['38', '43'])).
% 0.45/0.64  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      ((m1_subset_1 @ 
% 0.45/0.64        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.64  thf(redefinition_r2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.64          | ((X17) = (X20))
% 0.45/0.64          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.64             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 0.45/0.64          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.45/0.64        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.45/0.64            = (k6_partfun1 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['37', '48'])).
% 0.45/0.64  thf(t29_relset_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( m1_subset_1 @
% 0.45/0.64       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (![X21 : $i]:
% 0.45/0.64         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 0.45/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.45/0.64  thf(redefinition_k6_partfun1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.45/0.64  thf('51', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (![X21 : $i]:
% 0.45/0.64         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 0.45/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.45/0.64         = (k6_partfun1 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '52'])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t26_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ![E:$i]:
% 0.45/0.64         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.45/0.64             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.64           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.45/0.64             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.45/0.64               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.45/0.64         (~ (v1_funct_1 @ X41)
% 0.45/0.64          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.45/0.64          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.45/0.64          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X42 @ X42 @ X43 @ X45 @ X41))
% 0.45/0.64          | (v2_funct_1 @ X45)
% 0.45/0.64          | ((X43) = (k1_xboole_0))
% 0.45/0.64          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.45/0.64          | ~ (v1_funct_2 @ X45 @ X44 @ X42)
% 0.45/0.64          | ~ (v1_funct_1 @ X45))),
% 0.45/0.64      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.45/0.64          | ((sk_A) = (k1_xboole_0))
% 0.45/0.64          | (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ 
% 0.45/0.64               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 0.45/0.64          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.64  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.45/0.64          | ((sk_A) = (k1_xboole_0))
% 0.45/0.64          | (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ 
% 0.45/0.64               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 0.45/0.64      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.45/0.64        | (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((sk_A) = (k1_xboole_0))
% 0.45/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '59'])).
% 0.45/0.64  thf(fc4_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.45/0.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.45/0.64  thf('61', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.45/0.64  thf('62', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.64  thf('63', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 0.45/0.64      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf('64', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('67', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['60', '63', '64', '65', '66'])).
% 0.45/0.64  thf('68', plain, (~ (v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.45/0.64  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.64      inference('clc', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf(t113_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (![X1 : $i, X2 : $i]:
% 0.45/0.64         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.64  thf('71', plain,
% 0.45/0.64      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['70'])).
% 0.45/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.64  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['36', '69', '71', '72'])).
% 0.45/0.64  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['33', '73'])).
% 0.45/0.64  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.45/0.64  thf('75', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.45/0.64  thf('76', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.64  thf('77', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.45/0.64  thf('78', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 0.45/0.64      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf('79', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.45/0.64      inference('sup+', [status(thm)], ['77', '78'])).
% 0.45/0.64  thf('80', plain, ($false),
% 0.45/0.64      inference('demod', [status(thm)], ['32', '74', '79'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
