%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eKUkPt8qTK

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:06 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 297 expanded)
%              Number of leaves         :   38 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          : 1157 (5757 expanded)
%              Number of equality atoms :   32 (  69 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
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
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('19',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33 ) )
      | ( v2_funct_1 @ X37 )
      | ( X35 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X34 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
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
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
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

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['2','49'])).

thf('51',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','52'])).

thf('54',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_partfun1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('57',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_relat_1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['63','67','70','71','72','73'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != X18 )
      | ( v2_funct_2 @ X19 @ X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('76',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v5_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
      | ( v2_funct_2 @ X19 @ ( k2_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['63','67','70','71','72','73'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['77','80','81','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['53','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eKUkPt8qTK
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 375 iterations in 0.186s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.45/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(t29_funct_2, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ![D:$i]:
% 0.45/0.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.45/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.45/0.63           ( ( r2_relset_1 @
% 0.45/0.63               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.45/0.63               ( k6_partfun1 @ A ) ) =>
% 0.45/0.63             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.63        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.63            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63          ( ![D:$i]:
% 0.45/0.63            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.45/0.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.45/0.63              ( ( r2_relset_1 @
% 0.45/0.63                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.45/0.63                  ( k6_partfun1 @ A ) ) =>
% 0.45/0.63                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.45/0.63  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.63        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.63        (k6_partfun1 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k6_partfun1, axiom,
% 0.45/0.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.45/0.63  thf('4', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.63        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.63        (k6_relat_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k1_partfun1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.63         ( v1_funct_1 @ F ) & 
% 0.45/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.63       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.45/0.63         ( m1_subset_1 @
% 0.45/0.63           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.45/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.45/0.63          | ~ (v1_funct_1 @ X20)
% 0.45/0.63          | ~ (v1_funct_1 @ X23)
% 0.45/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.45/0.63          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.45/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.63          | ~ (v1_funct_1 @ X1)
% 0.45/0.63          | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.45/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.63          | ~ (v1_funct_1 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      ((~ (v1_funct_1 @ sk_D)
% 0.45/0.63        | (m1_subset_1 @ 
% 0.45/0.63           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['6', '11'])).
% 0.45/0.63  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      ((m1_subset_1 @ 
% 0.45/0.63        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf(redefinition_r2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.45/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.45/0.63          | ((X14) = (X17))
% 0.45/0.63          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.63             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.45/0.63          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.45/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.45/0.63        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.45/0.63            = (k6_relat_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '16'])).
% 0.45/0.63  thf(dt_k6_partfun1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( m1_subset_1 @
% 0.45/0.63         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.45/0.63       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X27 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.45/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.45/0.63  thf('19', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X27 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.45/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.45/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.45/0.63         = (k6_relat_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '20'])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t26_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ![E:$i]:
% 0.45/0.63         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.45/0.63             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.63           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.45/0.63             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.45/0.63               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X33)
% 0.45/0.63          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.45/0.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.45/0.63          | ~ (v2_funct_1 @ (k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33))
% 0.45/0.63          | (v2_funct_1 @ X37)
% 0.45/0.63          | ((X35) = (k1_xboole_0))
% 0.45/0.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.45/0.63          | ~ (v1_funct_2 @ X37 @ X36 @ X34)
% 0.45/0.63          | ~ (v1_funct_1 @ X37))),
% 0.45/0.63      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.63          | ((sk_A) = (k1_xboole_0))
% 0.45/0.63          | (v2_funct_1 @ X0)
% 0.45/0.63          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.45/0.63          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.45/0.63          | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.63          | ((sk_A) = (k1_xboole_0))
% 0.45/0.63          | (v2_funct_1 @ X0)
% 0.45/0.63          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.45/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.45/0.63        | (v2_funct_1 @ sk_C)
% 0.45/0.63        | ((sk_A) = (k1_xboole_0))
% 0.45/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.45/0.63        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '27'])).
% 0.45/0.63  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.45/0.63  thf('29', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('33', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.45/0.63  thf('34', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('35', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc3_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.63       ( ![C:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63           ( v1_xboole_0 @ C ) ) ) ))).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ X8)
% 0.45/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 0.45/0.63          | (v1_xboole_0 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.45/0.63  thf('38', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 0.45/0.63         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '38'])).
% 0.45/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.63  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.63  thf('41', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.63  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_funct_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.63       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc1_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( v1_relat_1 @ C ) ))).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.63         ((v1_relat_1 @ X2)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.63  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.63  thf('48', plain, ((~ (v1_xboole_0 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['44', '47'])).
% 0.45/0.63  thf('49', plain, (((v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['41', '48'])).
% 0.45/0.63  thf('50', plain, (((v2_funct_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['2', '49'])).
% 0.45/0.63  thf('51', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('52', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.45/0.63  thf('53', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['1', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.45/0.63         = (k6_relat_1 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '20'])).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t24_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ![D:$i]:
% 0.45/0.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.45/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.45/0.63           ( ( r2_relset_1 @
% 0.45/0.63               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.45/0.63               ( k6_partfun1 @ B ) ) =>
% 0.45/0.63             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X29)
% 0.45/0.63          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.45/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.45/0.63          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 0.45/0.63               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 0.45/0.63               (k6_partfun1 @ X30))
% 0.45/0.63          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 0.45/0.63          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.63          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.45/0.63          | ~ (v1_funct_1 @ X32))),
% 0.45/0.63      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.45/0.63  thf('57', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X29)
% 0.45/0.63          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.45/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.45/0.63          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 0.45/0.63               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 0.45/0.63               (k6_relat_1 @ X30))
% 0.45/0.63          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 0.45/0.63          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.63          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.45/0.63          | ~ (v1_funct_1 @ X32))),
% 0.45/0.63      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.45/0.63          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.45/0.63          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.63               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.45/0.63               (k6_relat_1 @ sk_A))
% 0.45/0.63          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.45/0.63          | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['55', '58'])).
% 0.45/0.63  thf('60', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_funct_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.45/0.63          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.45/0.63          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.63               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.45/0.63               (k6_relat_1 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.45/0.63           (k6_relat_1 @ sk_A))
% 0.45/0.63        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.45/0.63        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.45/0.63        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['54', '62'])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      (![X27 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.45/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.45/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.45/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.45/0.63          | (r2_relset_1 @ X15 @ X16 @ X14 @ X17)
% 0.45/0.63          | ((X14) != (X17)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.45/0.63  thf('66', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 0.45/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['64', '66'])).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.63         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.45/0.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('74', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['63', '67', '70', '71', '72', '73'])).
% 0.45/0.63  thf(d3_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.45/0.63       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i]:
% 0.45/0.63         (((k2_relat_1 @ X19) != (X18))
% 0.45/0.63          | (v2_funct_2 @ X19 @ X18)
% 0.45/0.63          | ~ (v5_relat_1 @ X19 @ X18)
% 0.45/0.63          | ~ (v1_relat_1 @ X19))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      (![X19 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X19)
% 0.45/0.63          | ~ (v5_relat_1 @ X19 @ (k2_relat_1 @ X19))
% 0.45/0.63          | (v2_funct_2 @ X19 @ (k2_relat_1 @ X19)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['75'])).
% 0.45/0.63  thf('77', plain,
% 0.45/0.63      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.45/0.63        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.45/0.63        | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['74', '76'])).
% 0.45/0.63  thf('78', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.63  thf('79', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.63         ((v5_relat_1 @ X5 @ X7)
% 0.45/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.63  thf('80', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.63  thf('81', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['63', '67', '70', '71', '72', '73'])).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.63         ((v1_relat_1 @ X2)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.63  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.63  thf('85', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['77', '80', '81', '84'])).
% 0.45/0.63  thf('86', plain, ($false), inference('demod', [status(thm)], ['53', '85'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
