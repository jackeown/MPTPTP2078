%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ziB42j8Oes

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:12 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 362 expanded)
%              Number of leaves         :   40 ( 123 expanded)
%              Depth                    :   18
%              Number of atoms          : 1184 (7125 expanded)
%              Number of equality atoms :   47 ( 105 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('18',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('19',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39 ) )
      | ( v2_funct_1 @ X43 )
      | ( X41 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('47',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','43','44','45','46'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('48',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('49',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('50',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['2','47','50'])).

thf('52',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('58',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_relat_1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['64','68','71','72','73','74'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('76',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != X24 )
      | ( v2_funct_2 @ X25 @ X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
      | ( v2_funct_2 @ X25 @ ( k2_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['64','68','71','72','73','74'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['78','81','82','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['54','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ziB42j8Oes
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 471 iterations in 0.275s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.53/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.53/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.53/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.74  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.53/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.74  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.53/0.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.74  thf(t29_funct_2, conjecture,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ![D:$i]:
% 0.53/0.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.74           ( ( r2_relset_1 @
% 0.53/0.74               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.74               ( k6_partfun1 @ A ) ) =>
% 0.53/0.74             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74          ( ![D:$i]:
% 0.53/0.74            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.74                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.74              ( ( r2_relset_1 @
% 0.53/0.74                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.74                  ( k6_partfun1 @ A ) ) =>
% 0.53/0.74                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.53/0.74  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('2', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.74        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.74        (k6_partfun1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(redefinition_k6_partfun1, axiom,
% 0.53/0.74    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.53/0.74  thf('4', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.74        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.74        (k6_relat_1 @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(dt_k1_partfun1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.74         ( v1_funct_1 @ F ) & 
% 0.53/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.53/0.74       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.53/0.74         ( m1_subset_1 @
% 0.53/0.74           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.53/0.74           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.53/0.74          | ~ (v1_funct_1 @ X26)
% 0.53/0.74          | ~ (v1_funct_1 @ X29)
% 0.53/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.53/0.74          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.53/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.53/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.53/0.74          | ~ (v1_funct_1 @ X1)
% 0.53/0.74          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.74  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.53/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.53/0.74          | ~ (v1_funct_1 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      ((~ (v1_funct_1 @ sk_D)
% 0.53/0.74        | (m1_subset_1 @ 
% 0.53/0.74           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['6', '11'])).
% 0.53/0.74  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      ((m1_subset_1 @ 
% 0.53/0.74        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['12', '13'])).
% 0.53/0.74  thf(redefinition_r2_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.53/0.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.53/0.74          | ((X20) = (X23))
% 0.53/0.74          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.74             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.53/0.74          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.53/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.53/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.53/0.74        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.74            = (k6_relat_1 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '16'])).
% 0.53/0.74  thf(dt_k6_partfun1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( m1_subset_1 @
% 0.53/0.74         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.53/0.74       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X33 : $i]:
% 0.53/0.74         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.53/0.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.53/0.74  thf('19', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X33 : $i]:
% 0.53/0.74         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.53/0.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.53/0.74      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.74         = (k6_relat_1 @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '20'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t26_funct_2, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ![E:$i]:
% 0.53/0.74         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.53/0.74             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.53/0.74           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.53/0.74             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.53/0.74               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X39)
% 0.53/0.74          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.53/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.53/0.74          | ~ (v2_funct_1 @ (k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39))
% 0.53/0.74          | (v2_funct_1 @ X43)
% 0.53/0.74          | ((X41) = (k1_xboole_0))
% 0.53/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 0.53/0.74          | ~ (v1_funct_2 @ X43 @ X42 @ X40)
% 0.53/0.74          | ~ (v1_funct_1 @ X43))),
% 0.53/0.74      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X0)
% 0.53/0.74          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.74          | ((sk_A) = (k1_xboole_0))
% 0.53/0.74          | (v2_funct_1 @ X0)
% 0.53/0.74          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.53/0.74          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.74          | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.74  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X0)
% 0.53/0.74          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.74          | ((sk_A) = (k1_xboole_0))
% 0.53/0.74          | (v2_funct_1 @ X0)
% 0.53/0.74          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.53/0.74      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.53/0.74        | (v2_funct_1 @ sk_C)
% 0.53/0.74        | ((sk_A) = (k1_xboole_0))
% 0.53/0.74        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.53/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['21', '27'])).
% 0.53/0.74  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.53/0.74  thf('29', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 0.53/0.74      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('33', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.53/0.74  thf('34', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('35', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t3_subset, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i]:
% 0.53/0.74         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.74  thf('38', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.74  thf(d10_xboole_0, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X0 : $i, X2 : $i]:
% 0.53/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 0.53/0.74        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B) @ sk_C)
% 0.53/0.74         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 0.53/0.74         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['35', '40'])).
% 0.53/0.74  thf(t113_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (![X5 : $i, X6 : $i]:
% 0.53/0.74         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.53/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.53/0.74  thf('44', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.53/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.74  thf('45', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.53/0.74  thf('47', plain, ((((k1_xboole_0) = (sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.74      inference('demod', [status(thm)], ['41', '43', '44', '45', '46'])).
% 0.53/0.74  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.53/0.74  thf('48', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.53/0.74  thf('49', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 0.53/0.74      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.53/0.74  thf('50', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.53/0.74      inference('sup+', [status(thm)], ['48', '49'])).
% 0.53/0.74  thf('51', plain, (((v2_funct_1 @ sk_C))),
% 0.53/0.74      inference('demod', [status(thm)], ['2', '47', '50'])).
% 0.53/0.74  thf('52', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 0.53/0.74      inference('split', [status(esa)], ['0'])).
% 0.53/0.74  thf('53', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.74      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.53/0.74  thf('54', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.74         = (k6_relat_1 @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '20'])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t24_funct_2, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ![D:$i]:
% 0.53/0.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.74           ( ( r2_relset_1 @
% 0.53/0.74               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.53/0.74               ( k6_partfun1 @ B ) ) =>
% 0.53/0.74             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X35)
% 0.53/0.74          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.53/0.74          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.53/0.74          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 0.53/0.74               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 0.53/0.74               (k6_partfun1 @ X36))
% 0.53/0.74          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 0.53/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.53/0.74          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.53/0.74          | ~ (v1_funct_1 @ X38))),
% 0.53/0.74      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.53/0.74  thf('58', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X35)
% 0.53/0.74          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.53/0.74          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.53/0.74          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 0.53/0.74               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 0.53/0.74               (k6_relat_1 @ X36))
% 0.53/0.74          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 0.53/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.53/0.74          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.53/0.74          | ~ (v1_funct_1 @ X38))),
% 0.53/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.53/0.74  thf('60', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X0)
% 0.53/0.74          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.74          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.74          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.74               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.74               (k6_relat_1 @ sk_A))
% 0.53/0.74          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.74          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['56', '59'])).
% 0.53/0.74  thf('61', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('63', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X0)
% 0.53/0.74          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.74          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.74          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.74               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.74               (k6_relat_1 @ sk_A)))),
% 0.53/0.74      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.53/0.74  thf('64', plain,
% 0.53/0.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.53/0.74           (k6_relat_1 @ sk_A))
% 0.53/0.74        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.53/0.74        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.74        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.74        | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['55', '63'])).
% 0.53/0.74  thf('65', plain,
% 0.53/0.74      (![X33 : $i]:
% 0.53/0.74         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.53/0.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.53/0.74      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.74  thf('66', plain,
% 0.53/0.74      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.53/0.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.53/0.74          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.53/0.74          | ((X20) != (X23)))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.74  thf('67', plain,
% 0.53/0.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.74         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.53/0.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['66'])).
% 0.53/0.74  thf('68', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['65', '67'])).
% 0.53/0.74  thf('69', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.74  thf('70', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.74         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.53/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.74  thf('71', plain,
% 0.53/0.74      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['69', '70'])).
% 0.53/0.74  thf('72', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('75', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['64', '68', '71', '72', '73', '74'])).
% 0.53/0.74  thf(d3_funct_2, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.53/0.74       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.53/0.74  thf('76', plain,
% 0.53/0.74      (![X24 : $i, X25 : $i]:
% 0.53/0.74         (((k2_relat_1 @ X25) != (X24))
% 0.53/0.74          | (v2_funct_2 @ X25 @ X24)
% 0.53/0.74          | ~ (v5_relat_1 @ X25 @ X24)
% 0.53/0.74          | ~ (v1_relat_1 @ X25))),
% 0.53/0.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.53/0.74  thf('77', plain,
% 0.53/0.74      (![X25 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X25)
% 0.53/0.74          | ~ (v5_relat_1 @ X25 @ (k2_relat_1 @ X25))
% 0.53/0.74          | (v2_funct_2 @ X25 @ (k2_relat_1 @ X25)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.53/0.74  thf('78', plain,
% 0.53/0.74      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.53/0.74        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.53/0.74        | ~ (v1_relat_1 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['75', '77'])).
% 0.53/0.74  thf('79', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(cc2_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.74  thf('80', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.74         ((v5_relat_1 @ X14 @ X16)
% 0.53/0.74          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.74  thf('81', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['79', '80'])).
% 0.53/0.74  thf('82', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['64', '68', '71', '72', '73', '74'])).
% 0.53/0.74  thf('83', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(cc1_relset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74       ( v1_relat_1 @ C ) ))).
% 0.53/0.74  thf('84', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.74         ((v1_relat_1 @ X11)
% 0.53/0.74          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.53/0.74  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.74      inference('sup-', [status(thm)], ['83', '84'])).
% 0.53/0.74  thf('86', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.53/0.74      inference('demod', [status(thm)], ['78', '81', '82', '85'])).
% 0.53/0.74  thf('87', plain, ($false), inference('demod', [status(thm)], ['54', '86'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
