%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bj6nqwuEfA

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:07 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 309 expanded)
%              Number of leaves         :   41 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          : 1049 (6300 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

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

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('16',plain,(
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

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != X23 )
      | ( v2_funct_2 @ X24 @ X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['31','34','35','38'])).

thf('40',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['13','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('51',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('58',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('61',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('62',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
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

thf('66',plain,(
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

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('78',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('79',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['47','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['44','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bj6nqwuEfA
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.33/2.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.52  % Solved by: fo/fo7.sh
% 2.33/2.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.52  % done 1771 iterations in 2.069s
% 2.33/2.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.52  % SZS output start Refutation
% 2.33/2.52  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.33/2.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.33/2.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.33/2.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.33/2.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.33/2.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.33/2.52  thf(sk_D_type, type, sk_D: $i).
% 2.33/2.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.33/2.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.33/2.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.33/2.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.33/2.52  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.33/2.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.33/2.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.33/2.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.33/2.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.33/2.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.33/2.52  thf(sk_C_type, type, sk_C: $i).
% 2.33/2.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.33/2.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.33/2.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.33/2.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.33/2.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.33/2.52  thf(t7_xboole_0, axiom,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.33/2.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.33/2.52  thf('0', plain,
% 2.33/2.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 2.33/2.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.33/2.52  thf(d1_xboole_0, axiom,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.33/2.52  thf('1', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.33/2.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.33/2.52  thf('2', plain,
% 2.33/2.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.33/2.52      inference('sup-', [status(thm)], ['0', '1'])).
% 2.33/2.52  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.33/2.52  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.33/2.52      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.33/2.52  thf(redefinition_k6_partfun1, axiom,
% 2.33/2.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.33/2.52  thf('4', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.33/2.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.33/2.52  thf('5', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.33/2.52      inference('demod', [status(thm)], ['3', '4'])).
% 2.33/2.52  thf(fc4_funct_1, axiom,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.33/2.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.33/2.52  thf('6', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 2.33/2.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.33/2.52  thf('7', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.33/2.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.33/2.52  thf('8', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 2.33/2.52      inference('demod', [status(thm)], ['6', '7'])).
% 2.33/2.52  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.33/2.52      inference('sup+', [status(thm)], ['5', '8'])).
% 2.33/2.52  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.33/2.52      inference('sup+', [status(thm)], ['2', '9'])).
% 2.33/2.52  thf(t29_funct_2, conjecture,
% 2.33/2.52    (![A:$i,B:$i,C:$i]:
% 2.33/2.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.33/2.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.33/2.52       ( ![D:$i]:
% 2.33/2.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.33/2.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.33/2.52           ( ( r2_relset_1 @
% 2.33/2.52               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.33/2.52               ( k6_partfun1 @ A ) ) =>
% 2.33/2.52             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.33/2.52  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.52    (~( ![A:$i,B:$i,C:$i]:
% 2.33/2.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.33/2.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.33/2.52          ( ![D:$i]:
% 2.33/2.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.33/2.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.33/2.52              ( ( r2_relset_1 @
% 2.33/2.52                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.33/2.52                  ( k6_partfun1 @ A ) ) =>
% 2.33/2.52                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.33/2.52    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.33/2.52  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.33/2.52      inference('split', [status(esa)], ['11'])).
% 2.33/2.52  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.33/2.52      inference('sup-', [status(thm)], ['10', '12'])).
% 2.33/2.52  thf('14', plain,
% 2.33/2.52      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.33/2.52        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D) @ 
% 2.33/2.52        (k6_partfun1 @ sk_A))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('15', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf(t24_funct_2, axiom,
% 2.33/2.52    (![A:$i,B:$i,C:$i]:
% 2.33/2.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.33/2.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.33/2.52       ( ![D:$i]:
% 2.33/2.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.33/2.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.33/2.52           ( ( r2_relset_1 @
% 2.33/2.52               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.33/2.52               ( k6_partfun1 @ B ) ) =>
% 2.33/2.52             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.33/2.52  thf('16', plain,
% 2.33/2.52      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.33/2.52         (~ (v1_funct_1 @ X32)
% 2.33/2.52          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 2.33/2.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.33/2.52          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 2.33/2.52               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 2.33/2.52               (k6_partfun1 @ X33))
% 2.33/2.52          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 2.33/2.52          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 2.33/2.52          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 2.33/2.52          | ~ (v1_funct_1 @ X35))),
% 2.33/2.52      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.33/2.52  thf('17', plain,
% 2.33/2.52      (![X0 : $i]:
% 2.33/2.52         (~ (v1_funct_1 @ X0)
% 2.33/2.52          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 2.33/2.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 2.33/2.52          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 2.33/2.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.33/2.52               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ X0) @ 
% 2.33/2.52               (k6_partfun1 @ sk_A))
% 2.33/2.52          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 2.33/2.52          | ~ (v1_funct_1 @ sk_C))),
% 2.33/2.52      inference('sup-', [status(thm)], ['15', '16'])).
% 2.33/2.52  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('20', plain,
% 2.33/2.52      (![X0 : $i]:
% 2.33/2.52         (~ (v1_funct_1 @ X0)
% 2.33/2.52          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 2.33/2.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 2.33/2.52          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 2.33/2.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.33/2.52               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ X0) @ 
% 2.33/2.52               (k6_partfun1 @ sk_A)))),
% 2.33/2.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.33/2.52  thf('21', plain,
% 2.33/2.52      ((((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (sk_A))
% 2.33/2.52        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 2.33/2.52        | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 2.33/2.52        | ~ (v1_funct_1 @ sk_D))),
% 2.33/2.52      inference('sup-', [status(thm)], ['14', '20'])).
% 2.33/2.52  thf('22', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf(redefinition_k2_relset_1, axiom,
% 2.33/2.52    (![A:$i,B:$i,C:$i]:
% 2.33/2.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.33/2.52  thf('23', plain,
% 2.33/2.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.33/2.52         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.33/2.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.33/2.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.33/2.52  thf('24', plain,
% 2.33/2.52      (((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.33/2.52      inference('sup-', [status(thm)], ['22', '23'])).
% 2.33/2.52  thf('25', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.33/2.52      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 2.33/2.52  thf(d3_funct_2, axiom,
% 2.33/2.52    (![A:$i,B:$i]:
% 2.33/2.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.33/2.52       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.33/2.52  thf('29', plain,
% 2.33/2.52      (![X23 : $i, X24 : $i]:
% 2.33/2.52         (((k2_relat_1 @ X24) != (X23))
% 2.33/2.52          | (v2_funct_2 @ X24 @ X23)
% 2.33/2.52          | ~ (v5_relat_1 @ X24 @ X23)
% 2.33/2.52          | ~ (v1_relat_1 @ X24))),
% 2.33/2.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.33/2.52  thf('30', plain,
% 2.33/2.52      (![X24 : $i]:
% 2.33/2.52         (~ (v1_relat_1 @ X24)
% 2.33/2.52          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 2.33/2.52          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 2.33/2.52      inference('simplify', [status(thm)], ['29'])).
% 2.33/2.52  thf('31', plain,
% 2.33/2.52      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.33/2.52        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.33/2.52        | ~ (v1_relat_1 @ sk_D))),
% 2.33/2.52      inference('sup-', [status(thm)], ['28', '30'])).
% 2.33/2.52  thf('32', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf(cc2_relset_1, axiom,
% 2.33/2.52    (![A:$i,B:$i,C:$i]:
% 2.33/2.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.33/2.52  thf('33', plain,
% 2.33/2.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.33/2.52         ((v5_relat_1 @ X9 @ X11)
% 2.33/2.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.33/2.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.33/2.52  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.33/2.52      inference('sup-', [status(thm)], ['32', '33'])).
% 2.33/2.52  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.33/2.52      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 2.33/2.52  thf('36', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf(cc1_relset_1, axiom,
% 2.33/2.52    (![A:$i,B:$i,C:$i]:
% 2.33/2.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.52       ( v1_relat_1 @ C ) ))).
% 2.33/2.52  thf('37', plain,
% 2.33/2.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.33/2.52         ((v1_relat_1 @ X6)
% 2.33/2.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.33/2.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.33/2.52  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 2.33/2.52      inference('sup-', [status(thm)], ['36', '37'])).
% 2.33/2.52  thf('39', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.33/2.52      inference('demod', [status(thm)], ['31', '34', '35', '38'])).
% 2.33/2.52  thf('40', plain,
% 2.33/2.52      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.33/2.52      inference('split', [status(esa)], ['11'])).
% 2.33/2.52  thf('41', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.33/2.52      inference('sup-', [status(thm)], ['39', '40'])).
% 2.33/2.52  thf('42', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.33/2.52      inference('split', [status(esa)], ['11'])).
% 2.33/2.52  thf('43', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.33/2.52      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 2.33/2.52  thf('44', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.33/2.52      inference('simpl_trail', [status(thm)], ['13', '43'])).
% 2.33/2.52  thf('45', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf(cc3_relset_1, axiom,
% 2.33/2.52    (![A:$i,B:$i]:
% 2.33/2.52     ( ( v1_xboole_0 @ A ) =>
% 2.33/2.52       ( ![C:$i]:
% 2.33/2.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.52           ( v1_xboole_0 @ C ) ) ) ))).
% 2.33/2.52  thf('46', plain,
% 2.33/2.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.33/2.52         (~ (v1_xboole_0 @ X12)
% 2.33/2.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 2.33/2.52          | (v1_xboole_0 @ X13))),
% 2.33/2.52      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.33/2.52  thf('47', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.33/2.52      inference('sup-', [status(thm)], ['45', '46'])).
% 2.33/2.52  thf('48', plain,
% 2.33/2.52      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.33/2.52        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D) @ 
% 2.33/2.52        (k6_partfun1 @ sk_A))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('49', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('50', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf(dt_k1_partfun1, axiom,
% 2.33/2.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.33/2.52     ( ( ( v1_funct_1 @ E ) & 
% 2.33/2.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.33/2.52         ( v1_funct_1 @ F ) & 
% 2.33/2.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.33/2.52       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.33/2.52         ( m1_subset_1 @
% 2.33/2.52           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.33/2.52           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.33/2.52  thf('51', plain,
% 2.33/2.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.33/2.52         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.33/2.52          | ~ (v1_funct_1 @ X25)
% 2.33/2.52          | ~ (v1_funct_1 @ X28)
% 2.33/2.52          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.33/2.52          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 2.33/2.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 2.33/2.52      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.33/2.52  thf('52', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.52         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.33/2.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.33/2.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.33/2.52          | ~ (v1_funct_1 @ X1)
% 2.33/2.52          | ~ (v1_funct_1 @ sk_C))),
% 2.33/2.52      inference('sup-', [status(thm)], ['50', '51'])).
% 2.33/2.52  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('54', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.52         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.33/2.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.33/2.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.33/2.52          | ~ (v1_funct_1 @ X1))),
% 2.33/2.52      inference('demod', [status(thm)], ['52', '53'])).
% 2.33/2.52  thf('55', plain,
% 2.33/2.52      ((~ (v1_funct_1 @ sk_D)
% 2.33/2.52        | (m1_subset_1 @ 
% 2.33/2.52           (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D) @ 
% 2.33/2.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.33/2.52      inference('sup-', [status(thm)], ['49', '54'])).
% 2.33/2.52  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('57', plain,
% 2.33/2.52      ((m1_subset_1 @ 
% 2.33/2.52        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D) @ 
% 2.33/2.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.33/2.52      inference('demod', [status(thm)], ['55', '56'])).
% 2.33/2.52  thf(redefinition_r2_relset_1, axiom,
% 2.33/2.52    (![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.33/2.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.33/2.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.33/2.52  thf('58', plain,
% 2.33/2.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.33/2.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.33/2.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.33/2.52          | ((X18) = (X21))
% 2.33/2.52          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 2.33/2.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.33/2.52  thf('59', plain,
% 2.33/2.52      (![X0 : $i]:
% 2.33/2.52         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.33/2.52             (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D) @ X0)
% 2.33/2.52          | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D) = (X0))
% 2.33/2.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.33/2.52      inference('sup-', [status(thm)], ['57', '58'])).
% 2.33/2.52  thf('60', plain,
% 2.33/2.52      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.33/2.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.33/2.52        | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D)
% 2.33/2.52            = (k6_partfun1 @ sk_A)))),
% 2.33/2.52      inference('sup-', [status(thm)], ['48', '59'])).
% 2.33/2.52  thf(t29_relset_1, axiom,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( m1_subset_1 @
% 2.33/2.52       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.33/2.52  thf('61', plain,
% 2.33/2.52      (![X22 : $i]:
% 2.33/2.52         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 2.33/2.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.33/2.52      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.33/2.52  thf('62', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.33/2.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.33/2.52  thf('63', plain,
% 2.33/2.52      (![X22 : $i]:
% 2.33/2.52         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 2.33/2.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.33/2.52      inference('demod', [status(thm)], ['61', '62'])).
% 2.33/2.52  thf('64', plain,
% 2.33/2.52      (((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C @ sk_D)
% 2.33/2.52         = (k6_partfun1 @ sk_A))),
% 2.33/2.52      inference('demod', [status(thm)], ['60', '63'])).
% 2.33/2.52  thf('65', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf(t26_funct_2, axiom,
% 2.33/2.52    (![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.33/2.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.33/2.52       ( ![E:$i]:
% 2.33/2.52         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.33/2.52             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.33/2.52           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.33/2.52             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.33/2.52               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.33/2.52  thf('66', plain,
% 2.33/2.52      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.33/2.52         (~ (v1_funct_1 @ X36)
% 2.33/2.52          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 2.33/2.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.33/2.52          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 2.33/2.52          | (v2_funct_1 @ X40)
% 2.33/2.52          | ((X38) = (k1_xboole_0))
% 2.33/2.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 2.33/2.52          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 2.33/2.52          | ~ (v1_funct_1 @ X40))),
% 2.33/2.52      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.33/2.52  thf('67', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (~ (v1_funct_1 @ X0)
% 2.33/2.52          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 2.33/2.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 2.33/2.52          | ((sk_A) = (k1_xboole_0))
% 2.33/2.52          | (v2_funct_1 @ X0)
% 2.33/2.52          | ~ (v2_funct_1 @ 
% 2.33/2.52               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D))
% 2.33/2.52          | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 2.33/2.52          | ~ (v1_funct_1 @ sk_D))),
% 2.33/2.52      inference('sup-', [status(thm)], ['65', '66'])).
% 2.33/2.52  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('70', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (~ (v1_funct_1 @ X0)
% 2.33/2.52          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 2.33/2.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 2.33/2.52          | ((sk_A) = (k1_xboole_0))
% 2.33/2.52          | (v2_funct_1 @ X0)
% 2.33/2.52          | ~ (v2_funct_1 @ 
% 2.33/2.52               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D)))),
% 2.33/2.52      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.33/2.52  thf('71', plain,
% 2.33/2.52      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.33/2.52        | (v2_funct_1 @ sk_C)
% 2.33/2.52        | ((sk_A) = (k1_xboole_0))
% 2.33/2.52        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 2.33/2.52        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 2.33/2.52        | ~ (v1_funct_1 @ sk_C))),
% 2.33/2.52      inference('sup-', [status(thm)], ['64', '70'])).
% 2.33/2.52  thf('72', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 2.33/2.52      inference('demod', [status(thm)], ['6', '7'])).
% 2.33/2.52  thf('73', plain,
% 2.33/2.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('74', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('76', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.33/2.52      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 2.33/2.52  thf('77', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.33/2.52      inference('split', [status(esa)], ['11'])).
% 2.33/2.52  thf('78', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.33/2.52      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 2.33/2.52  thf('79', plain, (~ (v2_funct_1 @ sk_C)),
% 2.33/2.52      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 2.33/2.52  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 2.33/2.52      inference('clc', [status(thm)], ['76', '79'])).
% 2.33/2.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.33/2.52  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.33/2.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.33/2.52  thf('82', plain, ((v1_xboole_0 @ sk_C)),
% 2.33/2.52      inference('demod', [status(thm)], ['47', '80', '81'])).
% 2.33/2.52  thf('83', plain, ($false), inference('demod', [status(thm)], ['44', '82'])).
% 2.33/2.52  
% 2.33/2.52  % SZS output end Refutation
% 2.33/2.52  
% 2.33/2.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
