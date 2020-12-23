%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oTgGWbJBj0

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:08 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 326 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          : 1090 (6571 expanded)
%              Number of equality atoms :   35 (  82 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('5',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

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

thf('7',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33 ) @ ( k6_partfun1 @ X31 ) )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
        = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('15',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33 ) @ ( k6_relat_1 @ X31 ) )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
        = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
       != X19 )
      | ( v2_funct_2 @ X20 @ X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v5_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
      | ( v2_funct_2 @ X20 @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
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
    inference(split,[status(esa)],['7'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['9','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('61',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('62',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X37 @ X35 @ X35 @ X36 @ X38 @ X34 ) )
      | ( v2_funct_1 @ X38 )
      | ( X36 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X35 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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
    inference(split,[status(esa)],['7'])).

thf('78',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('79',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','79'])).

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
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oTgGWbJBj0
% 0.14/0.37  % Computer   : n018.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:23:27 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 3.13/3.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.13/3.34  % Solved by: fo/fo7.sh
% 3.13/3.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.13/3.34  % done 2691 iterations in 2.846s
% 3.13/3.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.13/3.34  % SZS output start Refutation
% 3.13/3.34  thf(sk_D_type, type, sk_D: $i).
% 3.13/3.34  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.13/3.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.13/3.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.13/3.34  thf(sk_B_type, type, sk_B: $i).
% 3.13/3.34  thf(sk_A_type, type, sk_A: $i).
% 3.13/3.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.13/3.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.13/3.34  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.13/3.34  thf(sk_C_type, type, sk_C: $i).
% 3.13/3.34  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.13/3.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.13/3.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.13/3.34  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.13/3.34  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.13/3.34  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.13/3.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.13/3.34  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.13/3.34  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.13/3.34  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.13/3.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.13/3.34  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.13/3.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.13/3.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.13/3.34  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.13/3.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.13/3.34  thf(t8_boole, axiom,
% 3.13/3.34    (![A:$i,B:$i]:
% 3.13/3.34     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.13/3.34  thf('1', plain,
% 3.13/3.34      (![X0 : $i, X1 : $i]:
% 3.13/3.34         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.13/3.34      inference('cnf', [status(esa)], [t8_boole])).
% 3.13/3.34  thf('2', plain,
% 3.13/3.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.13/3.34      inference('sup-', [status(thm)], ['0', '1'])).
% 3.13/3.34  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.13/3.34  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.13/3.34      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.13/3.34  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.13/3.34  thf('4', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 3.13/3.34      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.13/3.34  thf('5', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.13/3.34      inference('sup+', [status(thm)], ['3', '4'])).
% 3.13/3.34  thf('6', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.13/3.34      inference('sup+', [status(thm)], ['2', '5'])).
% 3.13/3.34  thf(t29_funct_2, conjecture,
% 3.13/3.34    (![A:$i,B:$i,C:$i]:
% 3.13/3.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.13/3.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.34       ( ![D:$i]:
% 3.13/3.34         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.13/3.34             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.13/3.34           ( ( r2_relset_1 @
% 3.13/3.34               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.13/3.34               ( k6_partfun1 @ A ) ) =>
% 3.13/3.34             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.13/3.34  thf(zf_stmt_0, negated_conjecture,
% 3.13/3.34    (~( ![A:$i,B:$i,C:$i]:
% 3.13/3.34        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.13/3.34            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.34          ( ![D:$i]:
% 3.13/3.34            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.13/3.34                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.13/3.34              ( ( r2_relset_1 @
% 3.13/3.34                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.13/3.34                  ( k6_partfun1 @ A ) ) =>
% 3.13/3.34                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.13/3.34    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.13/3.34  thf('7', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('8', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.34      inference('split', [status(esa)], ['7'])).
% 3.13/3.34  thf('9', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.34      inference('sup-', [status(thm)], ['6', '8'])).
% 3.13/3.34  thf('10', plain,
% 3.13/3.34      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.34        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.34        (k6_partfun1 @ sk_A))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(redefinition_k6_partfun1, axiom,
% 3.13/3.34    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.13/3.34  thf('11', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.13/3.34      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.13/3.34  thf('12', plain,
% 3.13/3.34      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.34        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.34        (k6_relat_1 @ sk_A))),
% 3.13/3.34      inference('demod', [status(thm)], ['10', '11'])).
% 3.13/3.34  thf('13', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(t24_funct_2, axiom,
% 3.13/3.34    (![A:$i,B:$i,C:$i]:
% 3.13/3.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.13/3.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.34       ( ![D:$i]:
% 3.13/3.34         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.13/3.34             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.13/3.34           ( ( r2_relset_1 @
% 3.13/3.34               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.13/3.34               ( k6_partfun1 @ B ) ) =>
% 3.13/3.34             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.13/3.34  thf('14', plain,
% 3.13/3.34      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.13/3.34         (~ (v1_funct_1 @ X30)
% 3.13/3.34          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 3.13/3.34          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.13/3.34          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 3.13/3.34               (k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33) @ 
% 3.13/3.34               (k6_partfun1 @ X31))
% 3.13/3.34          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 3.13/3.34          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.13/3.34          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 3.13/3.34          | ~ (v1_funct_1 @ X33))),
% 3.13/3.34      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.13/3.34  thf('15', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.13/3.34      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.13/3.34  thf('16', plain,
% 3.13/3.34      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.13/3.34         (~ (v1_funct_1 @ X30)
% 3.13/3.34          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 3.13/3.34          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.13/3.34          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 3.13/3.34               (k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33) @ 
% 3.13/3.34               (k6_relat_1 @ X31))
% 3.13/3.34          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 3.13/3.34          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.13/3.34          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 3.13/3.34          | ~ (v1_funct_1 @ X33))),
% 3.13/3.34      inference('demod', [status(thm)], ['14', '15'])).
% 3.13/3.34  thf('17', plain,
% 3.13/3.34      (![X0 : $i]:
% 3.13/3.34         (~ (v1_funct_1 @ X0)
% 3.13/3.34          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.13/3.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.13/3.34          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.13/3.34          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.34               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.13/3.34               (k6_relat_1 @ sk_A))
% 3.13/3.34          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.13/3.34          | ~ (v1_funct_1 @ sk_C))),
% 3.13/3.34      inference('sup-', [status(thm)], ['13', '16'])).
% 3.13/3.34  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('20', plain,
% 3.13/3.34      (![X0 : $i]:
% 3.13/3.34         (~ (v1_funct_1 @ X0)
% 3.13/3.34          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.13/3.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.13/3.34          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.13/3.34          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.34               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.13/3.34               (k6_relat_1 @ sk_A)))),
% 3.13/3.34      inference('demod', [status(thm)], ['17', '18', '19'])).
% 3.13/3.34  thf('21', plain,
% 3.13/3.34      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.13/3.34        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.13/3.34        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.13/3.34        | ~ (v1_funct_1 @ sk_D))),
% 3.13/3.34      inference('sup-', [status(thm)], ['12', '20'])).
% 3.13/3.34  thf('22', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(redefinition_k2_relset_1, axiom,
% 3.13/3.34    (![A:$i,B:$i,C:$i]:
% 3.13/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.13/3.34       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.13/3.34  thf('23', plain,
% 3.13/3.34      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.13/3.34         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 3.13/3.34          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.13/3.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.13/3.34  thf('24', plain,
% 3.13/3.34      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.13/3.34      inference('sup-', [status(thm)], ['22', '23'])).
% 3.13/3.34  thf('25', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.13/3.34      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.13/3.34  thf(d3_funct_2, axiom,
% 3.13/3.34    (![A:$i,B:$i]:
% 3.13/3.34     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.13/3.34       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.13/3.34  thf('29', plain,
% 3.13/3.34      (![X19 : $i, X20 : $i]:
% 3.13/3.34         (((k2_relat_1 @ X20) != (X19))
% 3.13/3.34          | (v2_funct_2 @ X20 @ X19)
% 3.13/3.34          | ~ (v5_relat_1 @ X20 @ X19)
% 3.13/3.34          | ~ (v1_relat_1 @ X20))),
% 3.13/3.34      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.13/3.34  thf('30', plain,
% 3.13/3.34      (![X20 : $i]:
% 3.13/3.34         (~ (v1_relat_1 @ X20)
% 3.13/3.34          | ~ (v5_relat_1 @ X20 @ (k2_relat_1 @ X20))
% 3.13/3.34          | (v2_funct_2 @ X20 @ (k2_relat_1 @ X20)))),
% 3.13/3.34      inference('simplify', [status(thm)], ['29'])).
% 3.13/3.34  thf('31', plain,
% 3.13/3.34      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.13/3.34        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.13/3.34        | ~ (v1_relat_1 @ sk_D))),
% 3.13/3.34      inference('sup-', [status(thm)], ['28', '30'])).
% 3.13/3.34  thf('32', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(cc2_relset_1, axiom,
% 3.13/3.34    (![A:$i,B:$i,C:$i]:
% 3.13/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.13/3.34       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.13/3.34  thf('33', plain,
% 3.13/3.34      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.13/3.34         ((v5_relat_1 @ X6 @ X8)
% 3.13/3.34          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.13/3.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.13/3.34  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.13/3.34      inference('sup-', [status(thm)], ['32', '33'])).
% 3.13/3.34  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.13/3.34      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.13/3.34  thf('36', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(cc1_relset_1, axiom,
% 3.13/3.34    (![A:$i,B:$i,C:$i]:
% 3.13/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.13/3.34       ( v1_relat_1 @ C ) ))).
% 3.13/3.34  thf('37', plain,
% 3.13/3.34      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.13/3.34         ((v1_relat_1 @ X3)
% 3.13/3.34          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 3.13/3.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.13/3.34  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 3.13/3.34      inference('sup-', [status(thm)], ['36', '37'])).
% 3.13/3.34  thf('39', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.13/3.34      inference('demod', [status(thm)], ['31', '34', '35', '38'])).
% 3.13/3.34  thf('40', plain,
% 3.13/3.34      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.13/3.34      inference('split', [status(esa)], ['7'])).
% 3.13/3.34  thf('41', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.13/3.34      inference('sup-', [status(thm)], ['39', '40'])).
% 3.13/3.34  thf('42', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.13/3.34      inference('split', [status(esa)], ['7'])).
% 3.13/3.34  thf('43', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.13/3.34      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 3.13/3.34  thf('44', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.13/3.34      inference('simpl_trail', [status(thm)], ['9', '43'])).
% 3.13/3.34  thf('45', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(cc3_relset_1, axiom,
% 3.13/3.34    (![A:$i,B:$i]:
% 3.13/3.34     ( ( v1_xboole_0 @ A ) =>
% 3.13/3.34       ( ![C:$i]:
% 3.13/3.34         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.13/3.34           ( v1_xboole_0 @ C ) ) ) ))).
% 3.13/3.34  thf('46', plain,
% 3.13/3.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.13/3.34         (~ (v1_xboole_0 @ X9)
% 3.13/3.34          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 3.13/3.34          | (v1_xboole_0 @ X10))),
% 3.13/3.34      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.13/3.34  thf('47', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.13/3.34      inference('sup-', [status(thm)], ['45', '46'])).
% 3.13/3.34  thf('48', plain,
% 3.13/3.34      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.34        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.34        (k6_relat_1 @ sk_A))),
% 3.13/3.34      inference('demod', [status(thm)], ['10', '11'])).
% 3.13/3.34  thf('49', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('50', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(dt_k1_partfun1, axiom,
% 3.13/3.34    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.13/3.34     ( ( ( v1_funct_1 @ E ) & 
% 3.13/3.34         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.13/3.34         ( v1_funct_1 @ F ) & 
% 3.13/3.34         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.13/3.34       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.13/3.34         ( m1_subset_1 @
% 3.13/3.34           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.13/3.34           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.13/3.34  thf('51', plain,
% 3.13/3.34      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.13/3.34         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.13/3.34          | ~ (v1_funct_1 @ X21)
% 3.13/3.34          | ~ (v1_funct_1 @ X24)
% 3.13/3.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.13/3.34          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 3.13/3.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 3.13/3.34      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.13/3.34  thf('52', plain,
% 3.13/3.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.34         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.13/3.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.13/3.34          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.13/3.34          | ~ (v1_funct_1 @ X1)
% 3.13/3.34          | ~ (v1_funct_1 @ sk_C))),
% 3.13/3.34      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.34  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('54', plain,
% 3.13/3.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.34         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.13/3.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.13/3.34          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.13/3.34          | ~ (v1_funct_1 @ X1))),
% 3.13/3.34      inference('demod', [status(thm)], ['52', '53'])).
% 3.13/3.34  thf('55', plain,
% 3.13/3.34      ((~ (v1_funct_1 @ sk_D)
% 3.13/3.34        | (m1_subset_1 @ 
% 3.13/3.34           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.13/3.34      inference('sup-', [status(thm)], ['49', '54'])).
% 3.13/3.34  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('57', plain,
% 3.13/3.34      ((m1_subset_1 @ 
% 3.13/3.34        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.13/3.34      inference('demod', [status(thm)], ['55', '56'])).
% 3.13/3.34  thf(redefinition_r2_relset_1, axiom,
% 3.13/3.34    (![A:$i,B:$i,C:$i,D:$i]:
% 3.13/3.34     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.13/3.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.34       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.13/3.34  thf('58', plain,
% 3.13/3.34      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.13/3.34         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 3.13/3.34          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 3.13/3.34          | ((X15) = (X18))
% 3.13/3.34          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 3.13/3.34      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.13/3.34  thf('59', plain,
% 3.13/3.34      (![X0 : $i]:
% 3.13/3.34         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.34             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.13/3.34          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.13/3.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.13/3.34      inference('sup-', [status(thm)], ['57', '58'])).
% 3.13/3.34  thf('60', plain,
% 3.13/3.34      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.13/3.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.13/3.34        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.13/3.34            = (k6_relat_1 @ sk_A)))),
% 3.13/3.34      inference('sup-', [status(thm)], ['48', '59'])).
% 3.13/3.34  thf(dt_k6_partfun1, axiom,
% 3.13/3.34    (![A:$i]:
% 3.13/3.34     ( ( m1_subset_1 @
% 3.13/3.34         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.13/3.34       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.13/3.34  thf('61', plain,
% 3.13/3.34      (![X28 : $i]:
% 3.13/3.34         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 3.13/3.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 3.13/3.34      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.13/3.34  thf('62', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.13/3.34      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.13/3.34  thf('63', plain,
% 3.13/3.34      (![X28 : $i]:
% 3.13/3.34         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 3.13/3.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 3.13/3.34      inference('demod', [status(thm)], ['61', '62'])).
% 3.13/3.34  thf('64', plain,
% 3.13/3.34      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.13/3.34         = (k6_relat_1 @ sk_A))),
% 3.13/3.34      inference('demod', [status(thm)], ['60', '63'])).
% 3.13/3.34  thf('65', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf(t26_funct_2, axiom,
% 3.13/3.34    (![A:$i,B:$i,C:$i,D:$i]:
% 3.13/3.34     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.13/3.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.34       ( ![E:$i]:
% 3.13/3.34         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.13/3.34             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.13/3.34           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.13/3.34             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.13/3.34               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.13/3.34  thf('66', plain,
% 3.13/3.34      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.13/3.34         (~ (v1_funct_1 @ X34)
% 3.13/3.34          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 3.13/3.34          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.13/3.34          | ~ (v2_funct_1 @ (k1_partfun1 @ X37 @ X35 @ X35 @ X36 @ X38 @ X34))
% 3.13/3.34          | (v2_funct_1 @ X38)
% 3.13/3.34          | ((X36) = (k1_xboole_0))
% 3.13/3.34          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 3.13/3.34          | ~ (v1_funct_2 @ X38 @ X37 @ X35)
% 3.13/3.34          | ~ (v1_funct_1 @ X38))),
% 3.13/3.34      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.13/3.34  thf('67', plain,
% 3.13/3.34      (![X0 : $i, X1 : $i]:
% 3.13/3.34         (~ (v1_funct_1 @ X0)
% 3.13/3.34          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.13/3.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.13/3.34          | ((sk_A) = (k1_xboole_0))
% 3.13/3.34          | (v2_funct_1 @ X0)
% 3.13/3.34          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.13/3.34          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.13/3.34          | ~ (v1_funct_1 @ sk_D))),
% 3.13/3.34      inference('sup-', [status(thm)], ['65', '66'])).
% 3.13/3.34  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('70', plain,
% 3.13/3.34      (![X0 : $i, X1 : $i]:
% 3.13/3.34         (~ (v1_funct_1 @ X0)
% 3.13/3.34          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.13/3.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.13/3.34          | ((sk_A) = (k1_xboole_0))
% 3.13/3.34          | (v2_funct_1 @ X0)
% 3.13/3.34          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.13/3.34      inference('demod', [status(thm)], ['67', '68', '69'])).
% 3.13/3.34  thf('71', plain,
% 3.13/3.34      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.13/3.34        | (v2_funct_1 @ sk_C)
% 3.13/3.34        | ((sk_A) = (k1_xboole_0))
% 3.13/3.34        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.13/3.34        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.13/3.34        | ~ (v1_funct_1 @ sk_C))),
% 3.13/3.34      inference('sup-', [status(thm)], ['64', '70'])).
% 3.13/3.34  thf('72', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 3.13/3.34      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.13/3.34  thf('73', plain,
% 3.13/3.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('74', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 3.13/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.34  thf('76', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.13/3.34      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 3.13/3.34  thf('77', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.34      inference('split', [status(esa)], ['7'])).
% 3.13/3.34  thf('78', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.13/3.34      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 3.13/3.34  thf('79', plain, (~ (v2_funct_1 @ sk_C)),
% 3.13/3.34      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 3.13/3.34  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 3.13/3.34      inference('clc', [status(thm)], ['76', '79'])).
% 3.13/3.34  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.13/3.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.13/3.34  thf('82', plain, ((v1_xboole_0 @ sk_C)),
% 3.13/3.34      inference('demod', [status(thm)], ['47', '80', '81'])).
% 3.13/3.34  thf('83', plain, ($false), inference('demod', [status(thm)], ['44', '82'])).
% 3.13/3.34  
% 3.13/3.34  % SZS output end Refutation
% 3.13/3.34  
% 3.13/3.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
