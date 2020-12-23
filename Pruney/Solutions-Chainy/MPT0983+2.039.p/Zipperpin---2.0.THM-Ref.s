%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qk0V1wZPjg

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:07 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 454 expanded)
%              Number of leaves         :   44 ( 153 expanded)
%              Depth                    :   19
%              Number of atoms          : 1387 (6216 expanded)
%              Number of equality atoms :   68 ( 193 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
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
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('19',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48 ) )
      | ( v2_funct_1 @ X52 )
      | ( X50 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X49 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
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
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('44',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('46',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X23 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('55',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 )
      | ( X27 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('56',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('60',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','60'])).

thf('62',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('63',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k6_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 )
      | ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','72'])).

thf('74',plain,
    ( ( k1_xboole_0 = sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','73'])).

thf('75',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( k1_xboole_0 = sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','74'])).

thf('76',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('80',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('81',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['2','78','81'])).

thf('83',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('88',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('95',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('96',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('97',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('100',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('102',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('103',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['101','102'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('104',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('107',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('111',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['106','107'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['99','100','109','110','111','112','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('121',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('122',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['116','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['106','107'])).

thf('127',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['85','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qk0V1wZPjg
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.13/3.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.13/3.35  % Solved by: fo/fo7.sh
% 3.13/3.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.13/3.35  % done 4944 iterations in 2.882s
% 3.13/3.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.13/3.35  % SZS output start Refutation
% 3.13/3.35  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.13/3.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.13/3.35  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.13/3.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.13/3.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.13/3.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.13/3.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.13/3.35  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.13/3.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.13/3.35  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.13/3.35  thf(sk_D_type, type, sk_D: $i).
% 3.13/3.35  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.13/3.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.13/3.35  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.13/3.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.13/3.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.13/3.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.13/3.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.13/3.35  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.13/3.35  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.13/3.35  thf(sk_B_type, type, sk_B: $i).
% 3.13/3.35  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.13/3.35  thf(sk_A_type, type, sk_A: $i).
% 3.13/3.35  thf(sk_C_type, type, sk_C: $i).
% 3.13/3.35  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.13/3.35  thf(t29_funct_2, conjecture,
% 3.13/3.35    (![A:$i,B:$i,C:$i]:
% 3.13/3.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.13/3.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.35       ( ![D:$i]:
% 3.13/3.35         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.13/3.35             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.13/3.35           ( ( r2_relset_1 @
% 3.13/3.35               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.13/3.35               ( k6_partfun1 @ A ) ) =>
% 3.13/3.35             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.13/3.35  thf(zf_stmt_0, negated_conjecture,
% 3.13/3.35    (~( ![A:$i,B:$i,C:$i]:
% 3.13/3.35        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.13/3.35            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.35          ( ![D:$i]:
% 3.13/3.35            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.13/3.35                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.13/3.35              ( ( r2_relset_1 @
% 3.13/3.35                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.13/3.35                  ( k6_partfun1 @ A ) ) =>
% 3.13/3.35                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.13/3.35    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.13/3.35  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('1', plain,
% 3.13/3.35      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.13/3.35      inference('split', [status(esa)], ['0'])).
% 3.13/3.35  thf('2', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.35      inference('split', [status(esa)], ['0'])).
% 3.13/3.35  thf('3', plain,
% 3.13/3.35      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.35        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.35        (k6_partfun1 @ sk_A))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(redefinition_k6_partfun1, axiom,
% 3.13/3.35    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.13/3.35  thf('4', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.13/3.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.13/3.35  thf('5', plain,
% 3.13/3.35      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.35        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.35        (k6_relat_1 @ sk_A))),
% 3.13/3.35      inference('demod', [status(thm)], ['3', '4'])).
% 3.13/3.35  thf('6', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('7', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(dt_k1_partfun1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.13/3.35     ( ( ( v1_funct_1 @ E ) & 
% 3.13/3.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.13/3.35         ( v1_funct_1 @ F ) & 
% 3.13/3.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.13/3.35       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.13/3.35         ( m1_subset_1 @
% 3.13/3.35           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.13/3.35           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.13/3.35  thf('8', plain,
% 3.13/3.35      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.13/3.35          | ~ (v1_funct_1 @ X33)
% 3.13/3.35          | ~ (v1_funct_1 @ X36)
% 3.13/3.35          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.13/3.35          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 3.13/3.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 3.13/3.35      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.13/3.35  thf('9', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.13/3.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.13/3.35          | ~ (v1_funct_1 @ X1)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_C))),
% 3.13/3.35      inference('sup-', [status(thm)], ['7', '8'])).
% 3.13/3.35  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('11', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.35         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.13/3.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.13/3.35          | ~ (v1_funct_1 @ X1))),
% 3.13/3.35      inference('demod', [status(thm)], ['9', '10'])).
% 3.13/3.35  thf('12', plain,
% 3.13/3.35      ((~ (v1_funct_1 @ sk_D)
% 3.13/3.35        | (m1_subset_1 @ 
% 3.13/3.35           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['6', '11'])).
% 3.13/3.35  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('14', plain,
% 3.13/3.35      ((m1_subset_1 @ 
% 3.13/3.35        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.13/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.13/3.35      inference('demod', [status(thm)], ['12', '13'])).
% 3.13/3.35  thf(redefinition_r2_relset_1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i,D:$i]:
% 3.13/3.35     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.13/3.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.35       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.13/3.35  thf('15', plain,
% 3.13/3.35      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.13/3.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.13/3.35          | ((X27) = (X30))
% 3.13/3.35          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 3.13/3.35      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.13/3.35  thf('16', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.13/3.35             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.13/3.35          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['14', '15'])).
% 3.13/3.35  thf('17', plain,
% 3.13/3.35      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.13/3.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.13/3.35        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.13/3.35            = (k6_relat_1 @ sk_A)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['5', '16'])).
% 3.13/3.35  thf(dt_k6_partfun1, axiom,
% 3.13/3.35    (![A:$i]:
% 3.13/3.35     ( ( m1_subset_1 @
% 3.13/3.35         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.13/3.35       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.13/3.35  thf('18', plain,
% 3.13/3.35      (![X40 : $i]:
% 3.13/3.35         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 3.13/3.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.13/3.35      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.13/3.35  thf('19', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.13/3.35      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.13/3.35  thf('20', plain,
% 3.13/3.35      (![X40 : $i]:
% 3.13/3.35         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 3.13/3.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.13/3.35      inference('demod', [status(thm)], ['18', '19'])).
% 3.13/3.35  thf('21', plain,
% 3.13/3.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.13/3.35         = (k6_relat_1 @ sk_A))),
% 3.13/3.35      inference('demod', [status(thm)], ['17', '20'])).
% 3.13/3.35  thf('22', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(t26_funct_2, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i,D:$i]:
% 3.13/3.35     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.13/3.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.13/3.35       ( ![E:$i]:
% 3.13/3.35         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.13/3.35             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.13/3.35           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.13/3.35             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.13/3.35               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.13/3.35  thf('23', plain,
% 3.13/3.35      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.13/3.35         (~ (v1_funct_1 @ X48)
% 3.13/3.35          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 3.13/3.35          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 3.13/3.35          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48))
% 3.13/3.35          | (v2_funct_1 @ X52)
% 3.13/3.35          | ((X50) = (k1_xboole_0))
% 3.13/3.35          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 3.13/3.35          | ~ (v1_funct_2 @ X52 @ X51 @ X49)
% 3.13/3.35          | ~ (v1_funct_1 @ X52))),
% 3.13/3.35      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.13/3.35  thf('24', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (~ (v1_funct_1 @ X0)
% 3.13/3.35          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.13/3.35          | ((sk_A) = (k1_xboole_0))
% 3.13/3.35          | (v2_funct_1 @ X0)
% 3.13/3.35          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.13/3.35          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_D))),
% 3.13/3.35      inference('sup-', [status(thm)], ['22', '23'])).
% 3.13/3.35  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('27', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (~ (v1_funct_1 @ X0)
% 3.13/3.35          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.13/3.35          | ((sk_A) = (k1_xboole_0))
% 3.13/3.35          | (v2_funct_1 @ X0)
% 3.13/3.35          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.13/3.35      inference('demod', [status(thm)], ['24', '25', '26'])).
% 3.13/3.35  thf('28', plain,
% 3.13/3.35      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.13/3.35        | (v2_funct_1 @ sk_C)
% 3.13/3.35        | ((sk_A) = (k1_xboole_0))
% 3.13/3.35        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.13/3.35        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.13/3.35        | ~ (v1_funct_1 @ sk_C))),
% 3.13/3.35      inference('sup-', [status(thm)], ['21', '27'])).
% 3.13/3.35  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.13/3.35  thf('29', plain, (![X14 : $i]: (v2_funct_1 @ (k6_relat_1 @ X14))),
% 3.13/3.35      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.13/3.35  thf('30', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('33', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.13/3.35      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 3.13/3.35  thf('34', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.35      inference('split', [status(esa)], ['0'])).
% 3.13/3.35  thf('35', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['33', '34'])).
% 3.13/3.35  thf('36', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.13/3.35  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.13/3.35      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.13/3.35  thf(t8_boole, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.13/3.35  thf('38', plain,
% 3.13/3.35      (![X3 : $i, X4 : $i]:
% 3.13/3.35         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.13/3.35      inference('cnf', [status(esa)], [t8_boole])).
% 3.13/3.35  thf('39', plain,
% 3.13/3.35      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['37', '38'])).
% 3.13/3.35  thf('40', plain,
% 3.13/3.35      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['37', '38'])).
% 3.13/3.35  thf(t113_zfmisc_1, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.13/3.35       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.13/3.35  thf('41', plain,
% 3.13/3.35      (![X6 : $i, X7 : $i]:
% 3.13/3.35         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 3.13/3.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.13/3.35  thf('42', plain,
% 3.13/3.35      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.13/3.35      inference('simplify', [status(thm)], ['41'])).
% 3.13/3.35  thf('43', plain,
% 3.13/3.35      (![X40 : $i]:
% 3.13/3.35         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 3.13/3.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.13/3.35      inference('demod', [status(thm)], ['18', '19'])).
% 3.13/3.35  thf('44', plain,
% 3.13/3.35      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup+', [status(thm)], ['42', '43'])).
% 3.13/3.35  thf('45', plain,
% 3.13/3.35      (![X6 : $i, X7 : $i]:
% 3.13/3.35         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.13/3.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.13/3.35  thf('46', plain,
% 3.13/3.35      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 3.13/3.35      inference('simplify', [status(thm)], ['45'])).
% 3.13/3.35  thf(cc3_relset_1, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( v1_xboole_0 @ A ) =>
% 3.13/3.35       ( ![C:$i]:
% 3.13/3.35         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.13/3.35           ( v1_xboole_0 @ C ) ) ) ))).
% 3.13/3.35  thf('47', plain,
% 3.13/3.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.13/3.35         (~ (v1_xboole_0 @ X21)
% 3.13/3.35          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X23)))
% 3.13/3.35          | (v1_xboole_0 @ X22))),
% 3.13/3.35      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.13/3.35  thf('48', plain,
% 3.13/3.35      (![X1 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.13/3.35          | (v1_xboole_0 @ X1)
% 3.13/3.35          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['46', '47'])).
% 3.13/3.35  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.13/3.35      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.13/3.35  thf('50', plain,
% 3.13/3.35      (![X1 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.13/3.35          | (v1_xboole_0 @ X1))),
% 3.13/3.35      inference('demod', [status(thm)], ['48', '49'])).
% 3.13/3.35  thf('51', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['44', '50'])).
% 3.13/3.35  thf('52', plain,
% 3.13/3.35      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['37', '38'])).
% 3.13/3.35  thf('53', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['51', '52'])).
% 3.13/3.35  thf('54', plain,
% 3.13/3.35      (![X40 : $i]:
% 3.13/3.35         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 3.13/3.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.13/3.35      inference('demod', [status(thm)], ['18', '19'])).
% 3.13/3.35  thf('55', plain,
% 3.13/3.35      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.13/3.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.13/3.35          | (r2_relset_1 @ X28 @ X29 @ X27 @ X30)
% 3.13/3.35          | ((X27) != (X30)))),
% 3.13/3.35      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.13/3.35  thf('56', plain,
% 3.13/3.35      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.35         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 3.13/3.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.13/3.35      inference('simplify', [status(thm)], ['55'])).
% 3.13/3.35  thf('57', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['54', '56'])).
% 3.13/3.35  thf('58', plain,
% 3.13/3.35      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.13/3.35        (k6_relat_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup+', [status(thm)], ['53', '57'])).
% 3.13/3.35  thf('59', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['51', '52'])).
% 3.13/3.35  thf('60', plain,
% 3.13/3.35      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.13/3.35      inference('demod', [status(thm)], ['58', '59'])).
% 3.13/3.35  thf('61', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.13/3.35          | ~ (v1_xboole_0 @ X0))),
% 3.13/3.35      inference('sup+', [status(thm)], ['40', '60'])).
% 3.13/3.35  thf('62', plain,
% 3.13/3.35      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.13/3.35      inference('simplify', [status(thm)], ['41'])).
% 3.13/3.35  thf('63', plain,
% 3.13/3.35      (![X40 : $i]:
% 3.13/3.35         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 3.13/3.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.13/3.35      inference('demod', [status(thm)], ['18', '19'])).
% 3.13/3.35  thf('64', plain,
% 3.13/3.35      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.13/3.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.13/3.35          | ((X27) = (X30))
% 3.13/3.35          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 3.13/3.35      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.13/3.35  thf('65', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 3.13/3.35          | ((k6_relat_1 @ X0) = (X1))
% 3.13/3.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['63', '64'])).
% 3.13/3.35  thf('66', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.13/3.35          | ((k6_relat_1 @ k1_xboole_0) = (X0))
% 3.13/3.35          | ~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.13/3.35               (k6_relat_1 @ k1_xboole_0) @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['62', '65'])).
% 3.13/3.35  thf('67', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['51', '52'])).
% 3.13/3.35  thf('68', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['51', '52'])).
% 3.13/3.35  thf('69', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.13/3.35          | ((k1_xboole_0) = (X0))
% 3.13/3.35          | ~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 3.13/3.35      inference('demod', [status(thm)], ['66', '67', '68'])).
% 3.13/3.35  thf('70', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (v1_xboole_0 @ X0)
% 3.13/3.35          | ((k1_xboole_0) = (X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['61', '69'])).
% 3.13/3.35  thf('71', plain,
% 3.13/3.35      (![X1 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.13/3.35          | (v1_xboole_0 @ X1))),
% 3.13/3.35      inference('demod', [status(thm)], ['48', '49'])).
% 3.13/3.35  thf('72', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.13/3.35          | ((k1_xboole_0) = (X0)))),
% 3.13/3.35      inference('clc', [status(thm)], ['70', '71'])).
% 3.13/3.35  thf('73', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 3.13/3.35          | ~ (v1_xboole_0 @ X0)
% 3.13/3.35          | ((k1_xboole_0) = (X1)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['39', '72'])).
% 3.13/3.35  thf('74', plain,
% 3.13/3.35      ((((k1_xboole_0) = (sk_C))
% 3.13/3.35        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['36', '73'])).
% 3.13/3.35  thf('75', plain,
% 3.13/3.35      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 3.13/3.35         | ((k1_xboole_0) = (sk_C)))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['35', '74'])).
% 3.13/3.35  thf('76', plain,
% 3.13/3.35      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 3.13/3.35      inference('simplify', [status(thm)], ['45'])).
% 3.13/3.35  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.13/3.35      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.13/3.35  thf('78', plain, ((((k1_xboole_0) = (sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.13/3.35      inference('demod', [status(thm)], ['75', '76', '77'])).
% 3.13/3.35  thf('79', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['51', '52'])).
% 3.13/3.35  thf('80', plain, (![X14 : $i]: (v2_funct_1 @ (k6_relat_1 @ X14))),
% 3.13/3.35      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.13/3.35  thf('81', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.13/3.35      inference('sup+', [status(thm)], ['79', '80'])).
% 3.13/3.35  thf('82', plain, (((v2_funct_1 @ sk_C))),
% 3.13/3.35      inference('demod', [status(thm)], ['2', '78', '81'])).
% 3.13/3.35  thf('83', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.13/3.35      inference('split', [status(esa)], ['0'])).
% 3.13/3.35  thf('84', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.13/3.35      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 3.13/3.35  thf('85', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.13/3.35      inference('simpl_trail', [status(thm)], ['1', '84'])).
% 3.13/3.35  thf('86', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('87', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(redefinition_k1_partfun1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.13/3.35     ( ( ( v1_funct_1 @ E ) & 
% 3.13/3.35         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.13/3.35         ( v1_funct_1 @ F ) & 
% 3.13/3.35         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.13/3.35       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.13/3.35  thf('88', plain,
% 3.13/3.35      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 3.13/3.35         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 3.13/3.35          | ~ (v1_funct_1 @ X41)
% 3.13/3.35          | ~ (v1_funct_1 @ X44)
% 3.13/3.35          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.13/3.35          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 3.13/3.35              = (k5_relat_1 @ X41 @ X44)))),
% 3.13/3.35      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.13/3.35  thf('89', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.13/3.35            = (k5_relat_1 @ sk_C @ X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.13/3.35          | ~ (v1_funct_1 @ X0)
% 3.13/3.35          | ~ (v1_funct_1 @ sk_C))),
% 3.13/3.35      inference('sup-', [status(thm)], ['87', '88'])).
% 3.13/3.35  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('91', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.35         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.13/3.35            = (k5_relat_1 @ sk_C @ X0))
% 3.13/3.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.13/3.35          | ~ (v1_funct_1 @ X0))),
% 3.13/3.35      inference('demod', [status(thm)], ['89', '90'])).
% 3.13/3.35  thf('92', plain,
% 3.13/3.35      ((~ (v1_funct_1 @ sk_D)
% 3.13/3.35        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.13/3.35            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['86', '91'])).
% 3.13/3.35  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('94', plain,
% 3.13/3.35      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.13/3.35         = (k6_relat_1 @ sk_A))),
% 3.13/3.35      inference('demod', [status(thm)], ['17', '20'])).
% 3.13/3.35  thf('95', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.13/3.35      inference('demod', [status(thm)], ['92', '93', '94'])).
% 3.13/3.35  thf(t45_relat_1, axiom,
% 3.13/3.35    (![A:$i]:
% 3.13/3.35     ( ( v1_relat_1 @ A ) =>
% 3.13/3.35       ( ![B:$i]:
% 3.13/3.35         ( ( v1_relat_1 @ B ) =>
% 3.13/3.35           ( r1_tarski @
% 3.13/3.35             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.13/3.35  thf('96', plain,
% 3.13/3.35      (![X10 : $i, X11 : $i]:
% 3.13/3.35         (~ (v1_relat_1 @ X10)
% 3.13/3.35          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 3.13/3.35             (k2_relat_1 @ X10))
% 3.13/3.35          | ~ (v1_relat_1 @ X11))),
% 3.13/3.35      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.13/3.35  thf(d10_xboole_0, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.13/3.35  thf('97', plain,
% 3.13/3.35      (![X0 : $i, X2 : $i]:
% 3.13/3.35         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.13/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.13/3.35  thf('98', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (~ (v1_relat_1 @ X1)
% 3.13/3.35          | ~ (v1_relat_1 @ X0)
% 3.13/3.35          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.13/3.35               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.13/3.35          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['96', '97'])).
% 3.13/3.35  thf('99', plain,
% 3.13/3.35      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k2_relat_1 @ (k6_relat_1 @ sk_A)))
% 3.13/3.35        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.13/3.35        | ~ (v1_relat_1 @ sk_D)
% 3.13/3.35        | ~ (v1_relat_1 @ sk_C))),
% 3.13/3.35      inference('sup-', [status(thm)], ['95', '98'])).
% 3.13/3.35  thf(t71_relat_1, axiom,
% 3.13/3.35    (![A:$i]:
% 3.13/3.35     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.13/3.35       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.13/3.35  thf('100', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 3.13/3.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.13/3.35  thf('101', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(cc2_relset_1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i]:
% 3.13/3.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.13/3.35       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.13/3.35  thf('102', plain,
% 3.13/3.35      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.13/3.35         ((v5_relat_1 @ X18 @ X20)
% 3.13/3.35          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.13/3.35      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.13/3.35  thf('103', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.13/3.35      inference('sup-', [status(thm)], ['101', '102'])).
% 3.13/3.35  thf(d19_relat_1, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( v1_relat_1 @ B ) =>
% 3.13/3.35       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.13/3.35  thf('104', plain,
% 3.13/3.35      (![X8 : $i, X9 : $i]:
% 3.13/3.35         (~ (v5_relat_1 @ X8 @ X9)
% 3.13/3.35          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 3.13/3.35          | ~ (v1_relat_1 @ X8))),
% 3.13/3.35      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.13/3.35  thf('105', plain,
% 3.13/3.35      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.13/3.35      inference('sup-', [status(thm)], ['103', '104'])).
% 3.13/3.35  thf('106', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf(cc1_relset_1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i]:
% 3.13/3.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.13/3.35       ( v1_relat_1 @ C ) ))).
% 3.13/3.35  thf('107', plain,
% 3.13/3.35      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.13/3.35         ((v1_relat_1 @ X15)
% 3.13/3.35          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.13/3.35      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.13/3.35  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 3.13/3.35      inference('sup-', [status(thm)], ['106', '107'])).
% 3.13/3.35  thf('109', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.13/3.35      inference('demod', [status(thm)], ['105', '108'])).
% 3.13/3.35  thf('110', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.13/3.35      inference('demod', [status(thm)], ['92', '93', '94'])).
% 3.13/3.35  thf('111', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 3.13/3.35      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.13/3.35  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 3.13/3.35      inference('sup-', [status(thm)], ['106', '107'])).
% 3.13/3.35  thf('113', plain,
% 3.13/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('114', plain,
% 3.13/3.35      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.13/3.35         ((v1_relat_1 @ X15)
% 3.13/3.35          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.13/3.35      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.13/3.35  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 3.13/3.35      inference('sup-', [status(thm)], ['113', '114'])).
% 3.13/3.35  thf('116', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.13/3.35      inference('demod', [status(thm)],
% 3.13/3.35                ['99', '100', '109', '110', '111', '112', '115'])).
% 3.13/3.35  thf('117', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.13/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.13/3.35  thf('118', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.13/3.35      inference('simplify', [status(thm)], ['117'])).
% 3.13/3.35  thf('119', plain,
% 3.13/3.35      (![X8 : $i, X9 : $i]:
% 3.13/3.35         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 3.13/3.35          | (v5_relat_1 @ X8 @ X9)
% 3.13/3.35          | ~ (v1_relat_1 @ X8))),
% 3.13/3.35      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.13/3.35  thf('120', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['118', '119'])).
% 3.13/3.35  thf(d3_funct_2, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.13/3.35       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.13/3.35  thf('121', plain,
% 3.13/3.35      (![X31 : $i, X32 : $i]:
% 3.13/3.35         (((k2_relat_1 @ X32) != (X31))
% 3.13/3.35          | (v2_funct_2 @ X32 @ X31)
% 3.13/3.35          | ~ (v5_relat_1 @ X32 @ X31)
% 3.13/3.35          | ~ (v1_relat_1 @ X32))),
% 3.13/3.35      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.13/3.35  thf('122', plain,
% 3.13/3.35      (![X32 : $i]:
% 3.13/3.35         (~ (v1_relat_1 @ X32)
% 3.13/3.35          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 3.13/3.35          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 3.13/3.35      inference('simplify', [status(thm)], ['121'])).
% 3.13/3.35  thf('123', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (v1_relat_1 @ X0)
% 3.13/3.35          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.13/3.35          | ~ (v1_relat_1 @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['120', '122'])).
% 3.13/3.35  thf('124', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.13/3.35      inference('simplify', [status(thm)], ['123'])).
% 3.13/3.35  thf('125', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.13/3.35      inference('sup+', [status(thm)], ['116', '124'])).
% 3.13/3.35  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 3.13/3.35      inference('sup-', [status(thm)], ['106', '107'])).
% 3.13/3.35  thf('127', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.13/3.35      inference('demod', [status(thm)], ['125', '126'])).
% 3.13/3.35  thf('128', plain, ($false), inference('demod', [status(thm)], ['85', '127'])).
% 3.13/3.35  
% 3.13/3.35  % SZS output end Refutation
% 3.13/3.35  
% 3.13/3.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
