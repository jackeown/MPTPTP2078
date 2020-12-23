%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z54ONfU6qX

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:05 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 292 expanded)
%              Number of leaves         :   38 ( 101 expanded)
%              Depth                    :   18
%              Number of atoms          : 1190 (5565 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('14',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
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

thf('36',plain,(
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

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','54','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['17','56'])).

thf('58',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('62',plain,(
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

thf('63',plain,(
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

thf('64',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
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
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['70','74','77','78','79','80'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('83',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('86',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['70','74','77','78','79','80'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('90',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['84','87','88','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['60','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z54ONfU6qX
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:10:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 2.58/2.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.58/2.82  % Solved by: fo/fo7.sh
% 2.58/2.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.58/2.82  % done 3402 iterations in 2.352s
% 2.58/2.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.58/2.82  % SZS output start Refutation
% 2.58/2.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.58/2.82  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.58/2.82  thf(sk_A_type, type, sk_A: $i).
% 2.58/2.82  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.58/2.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.58/2.82  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.58/2.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.58/2.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.58/2.82  thf(sk_B_type, type, sk_B: $i).
% 2.58/2.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.58/2.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.58/2.82  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.58/2.82  thf(sk_C_type, type, sk_C: $i).
% 2.58/2.82  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.58/2.82  thf(sk_D_type, type, sk_D: $i).
% 2.58/2.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.58/2.82  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.58/2.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.58/2.82  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.58/2.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.58/2.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.58/2.82  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.58/2.82  thf(t29_funct_2, conjecture,
% 2.58/2.82    (![A:$i,B:$i,C:$i]:
% 2.58/2.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.58/2.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.58/2.82       ( ![D:$i]:
% 2.58/2.82         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.58/2.82             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.58/2.82           ( ( r2_relset_1 @
% 2.58/2.82               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.58/2.82               ( k6_partfun1 @ A ) ) =>
% 2.58/2.82             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.58/2.82  thf(zf_stmt_0, negated_conjecture,
% 2.58/2.82    (~( ![A:$i,B:$i,C:$i]:
% 2.58/2.82        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.58/2.82            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.58/2.82          ( ![D:$i]:
% 2.58/2.82            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.58/2.82                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.58/2.82              ( ( r2_relset_1 @
% 2.58/2.82                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.58/2.82                  ( k6_partfun1 @ A ) ) =>
% 2.58/2.82                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.58/2.82    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.58/2.82  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('1', plain,
% 2.58/2.82      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.58/2.82      inference('split', [status(esa)], ['0'])).
% 2.58/2.82  thf(l13_xboole_0, axiom,
% 2.58/2.82    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.58/2.82  thf('2', plain,
% 2.58/2.82      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.58/2.82      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.58/2.82  thf(t113_zfmisc_1, axiom,
% 2.58/2.82    (![A:$i,B:$i]:
% 2.58/2.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.58/2.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.58/2.82  thf('3', plain,
% 2.58/2.82      (![X2 : $i, X3 : $i]:
% 2.58/2.82         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.58/2.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.58/2.82  thf('4', plain,
% 2.58/2.82      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 2.58/2.82      inference('simplify', [status(thm)], ['3'])).
% 2.58/2.82  thf(t29_relset_1, axiom,
% 2.58/2.82    (![A:$i]:
% 2.58/2.82     ( m1_subset_1 @
% 2.58/2.82       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.58/2.82  thf('5', plain,
% 2.58/2.82      (![X20 : $i]:
% 2.58/2.82         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 2.58/2.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 2.58/2.82      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.58/2.82  thf(cc1_subset_1, axiom,
% 2.58/2.82    (![A:$i]:
% 2.58/2.82     ( ( v1_xboole_0 @ A ) =>
% 2.58/2.82       ( ![B:$i]:
% 2.58/2.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 2.58/2.82  thf('6', plain,
% 2.58/2.82      (![X4 : $i, X5 : $i]:
% 2.58/2.82         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.58/2.82          | (v1_xboole_0 @ X4)
% 2.58/2.82          | ~ (v1_xboole_0 @ X5))),
% 2.58/2.82      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.58/2.82  thf('7', plain,
% 2.58/2.82      (![X0 : $i]:
% 2.58/2.82         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.58/2.82          | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 2.58/2.82      inference('sup-', [status(thm)], ['5', '6'])).
% 2.58/2.82  thf('8', plain,
% 2.58/2.82      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.58/2.82        | (v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0)))),
% 2.58/2.82      inference('sup-', [status(thm)], ['4', '7'])).
% 2.58/2.82  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.58/2.82  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.58/2.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.58/2.82  thf('10', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 2.58/2.82      inference('demod', [status(thm)], ['8', '9'])).
% 2.58/2.82  thf('11', plain,
% 2.58/2.82      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.58/2.82      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.58/2.82  thf('12', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.58/2.82      inference('sup-', [status(thm)], ['10', '11'])).
% 2.58/2.82  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.58/2.82  thf('13', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 2.58/2.82      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.58/2.82  thf('14', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.58/2.82      inference('sup+', [status(thm)], ['12', '13'])).
% 2.58/2.82  thf('15', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.58/2.82      inference('sup+', [status(thm)], ['2', '14'])).
% 2.58/2.82  thf('16', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.58/2.82      inference('split', [status(esa)], ['0'])).
% 2.58/2.82  thf('17', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.58/2.82      inference('sup-', [status(thm)], ['15', '16'])).
% 2.58/2.82  thf('18', plain,
% 2.58/2.82      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.58/2.82        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.58/2.82        (k6_partfun1 @ sk_A))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf(redefinition_k6_partfun1, axiom,
% 2.58/2.82    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.58/2.82  thf('19', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 2.58/2.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.58/2.82  thf('20', plain,
% 2.58/2.82      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.58/2.82        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.58/2.82        (k6_relat_1 @ sk_A))),
% 2.58/2.82      inference('demod', [status(thm)], ['18', '19'])).
% 2.58/2.82  thf('21', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('22', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf(dt_k1_partfun1, axiom,
% 2.58/2.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.58/2.82     ( ( ( v1_funct_1 @ E ) & 
% 2.58/2.82         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.58/2.82         ( v1_funct_1 @ F ) & 
% 2.58/2.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.58/2.82       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.58/2.82         ( m1_subset_1 @
% 2.58/2.82           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.58/2.82           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.58/2.82  thf('23', plain,
% 2.58/2.82      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.58/2.82         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.58/2.82          | ~ (v1_funct_1 @ X23)
% 2.58/2.82          | ~ (v1_funct_1 @ X26)
% 2.58/2.82          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.58/2.82          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 2.58/2.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 2.58/2.82      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.58/2.82  thf('24', plain,
% 2.58/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.82         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.58/2.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.58/2.82          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.58/2.82          | ~ (v1_funct_1 @ X1)
% 2.58/2.82          | ~ (v1_funct_1 @ sk_C))),
% 2.58/2.82      inference('sup-', [status(thm)], ['22', '23'])).
% 2.58/2.82  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('26', plain,
% 2.58/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.58/2.82         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.58/2.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.58/2.82          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.58/2.82          | ~ (v1_funct_1 @ X1))),
% 2.58/2.82      inference('demod', [status(thm)], ['24', '25'])).
% 2.58/2.82  thf('27', plain,
% 2.58/2.82      ((~ (v1_funct_1 @ sk_D)
% 2.58/2.82        | (m1_subset_1 @ 
% 2.58/2.82           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.58/2.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.58/2.82      inference('sup-', [status(thm)], ['21', '26'])).
% 2.58/2.82  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('29', plain,
% 2.58/2.82      ((m1_subset_1 @ 
% 2.58/2.82        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.58/2.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.58/2.82      inference('demod', [status(thm)], ['27', '28'])).
% 2.58/2.82  thf(redefinition_r2_relset_1, axiom,
% 2.58/2.82    (![A:$i,B:$i,C:$i,D:$i]:
% 2.58/2.82     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.58/2.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.58/2.82       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.58/2.82  thf('30', plain,
% 2.58/2.82      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.58/2.82         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.58/2.82          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.58/2.82          | ((X16) = (X19))
% 2.58/2.82          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 2.58/2.82      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.58/2.82  thf('31', plain,
% 2.58/2.82      (![X0 : $i]:
% 2.58/2.82         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.58/2.82             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.58/2.82          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.58/2.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.58/2.82      inference('sup-', [status(thm)], ['29', '30'])).
% 2.58/2.82  thf('32', plain,
% 2.58/2.82      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.58/2.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.58/2.82        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.58/2.82            = (k6_relat_1 @ sk_A)))),
% 2.58/2.82      inference('sup-', [status(thm)], ['20', '31'])).
% 2.58/2.82  thf('33', plain,
% 2.58/2.82      (![X20 : $i]:
% 2.58/2.82         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 2.58/2.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 2.58/2.82      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.58/2.82  thf('34', plain,
% 2.58/2.82      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.58/2.82         = (k6_relat_1 @ sk_A))),
% 2.58/2.82      inference('demod', [status(thm)], ['32', '33'])).
% 2.58/2.82  thf('35', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf(t26_funct_2, axiom,
% 2.58/2.82    (![A:$i,B:$i,C:$i,D:$i]:
% 2.58/2.82     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.58/2.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.58/2.82       ( ![E:$i]:
% 2.58/2.82         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.58/2.82             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.58/2.82           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.58/2.82             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.58/2.82               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.58/2.82  thf('36', plain,
% 2.58/2.82      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.58/2.82         (~ (v1_funct_1 @ X34)
% 2.58/2.82          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 2.58/2.82          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.58/2.82          | ~ (v2_funct_1 @ (k1_partfun1 @ X37 @ X35 @ X35 @ X36 @ X38 @ X34))
% 2.58/2.82          | (v2_funct_1 @ X38)
% 2.58/2.82          | ((X36) = (k1_xboole_0))
% 2.58/2.82          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 2.58/2.82          | ~ (v1_funct_2 @ X38 @ X37 @ X35)
% 2.58/2.82          | ~ (v1_funct_1 @ X38))),
% 2.58/2.82      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.58/2.82  thf('37', plain,
% 2.58/2.82      (![X0 : $i, X1 : $i]:
% 2.58/2.82         (~ (v1_funct_1 @ X0)
% 2.58/2.82          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.58/2.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.58/2.82          | ((sk_A) = (k1_xboole_0))
% 2.58/2.82          | (v2_funct_1 @ X0)
% 2.58/2.82          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.58/2.82          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.58/2.82          | ~ (v1_funct_1 @ sk_D))),
% 2.58/2.82      inference('sup-', [status(thm)], ['35', '36'])).
% 2.58/2.82  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('40', plain,
% 2.58/2.82      (![X0 : $i, X1 : $i]:
% 2.58/2.82         (~ (v1_funct_1 @ X0)
% 2.58/2.82          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.58/2.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.58/2.82          | ((sk_A) = (k1_xboole_0))
% 2.58/2.82          | (v2_funct_1 @ X0)
% 2.58/2.82          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.58/2.82      inference('demod', [status(thm)], ['37', '38', '39'])).
% 2.58/2.82  thf('41', plain,
% 2.58/2.82      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.58/2.82        | (v2_funct_1 @ sk_C)
% 2.58/2.82        | ((sk_A) = (k1_xboole_0))
% 2.58/2.82        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.58/2.82        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.58/2.82        | ~ (v1_funct_1 @ sk_C))),
% 2.58/2.82      inference('sup-', [status(thm)], ['34', '40'])).
% 2.58/2.82  thf('42', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 2.58/2.82      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.58/2.82  thf('43', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('44', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('46', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.58/2.82      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 2.58/2.82  thf('47', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.58/2.82      inference('split', [status(esa)], ['0'])).
% 2.58/2.82  thf('48', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.58/2.82      inference('sup-', [status(thm)], ['46', '47'])).
% 2.58/2.82  thf('49', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('50', plain,
% 2.58/2.82      (![X4 : $i, X5 : $i]:
% 2.58/2.82         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.58/2.82          | (v1_xboole_0 @ X4)
% 2.58/2.82          | ~ (v1_xboole_0 @ X5))),
% 2.58/2.82      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.58/2.82  thf('51', plain,
% 2.58/2.82      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 2.58/2.82      inference('sup-', [status(thm)], ['49', '50'])).
% 2.58/2.82  thf('52', plain,
% 2.58/2.82      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 2.58/2.82         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.58/2.82      inference('sup-', [status(thm)], ['48', '51'])).
% 2.58/2.82  thf('53', plain,
% 2.58/2.82      (![X2 : $i, X3 : $i]:
% 2.58/2.82         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 2.58/2.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.58/2.82  thf('54', plain,
% 2.58/2.82      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.58/2.82      inference('simplify', [status(thm)], ['53'])).
% 2.58/2.82  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.58/2.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.58/2.82  thf('56', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.58/2.82      inference('demod', [status(thm)], ['52', '54', '55'])).
% 2.58/2.82  thf('57', plain, (((v2_funct_1 @ sk_C))),
% 2.58/2.82      inference('demod', [status(thm)], ['17', '56'])).
% 2.58/2.82  thf('58', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 2.58/2.82      inference('split', [status(esa)], ['0'])).
% 2.58/2.82  thf('59', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.58/2.82      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 2.58/2.82  thf('60', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 2.58/2.82      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 2.58/2.82  thf('61', plain,
% 2.58/2.82      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.58/2.82         = (k6_relat_1 @ sk_A))),
% 2.58/2.82      inference('demod', [status(thm)], ['32', '33'])).
% 2.58/2.82  thf('62', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf(t24_funct_2, axiom,
% 2.58/2.82    (![A:$i,B:$i,C:$i]:
% 2.58/2.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.58/2.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.58/2.82       ( ![D:$i]:
% 2.58/2.82         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.58/2.82             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.58/2.82           ( ( r2_relset_1 @
% 2.58/2.82               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.58/2.82               ( k6_partfun1 @ B ) ) =>
% 2.58/2.82             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.58/2.82  thf('63', plain,
% 2.58/2.82      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.58/2.82         (~ (v1_funct_1 @ X30)
% 2.58/2.82          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 2.58/2.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.58/2.82          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 2.58/2.82               (k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33) @ 
% 2.58/2.82               (k6_partfun1 @ X31))
% 2.58/2.82          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 2.58/2.82          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 2.58/2.82          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 2.58/2.82          | ~ (v1_funct_1 @ X33))),
% 2.58/2.82      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.58/2.82  thf('64', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 2.58/2.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.58/2.82  thf('65', plain,
% 2.58/2.82      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.58/2.82         (~ (v1_funct_1 @ X30)
% 2.58/2.82          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 2.58/2.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.58/2.82          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 2.58/2.82               (k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33) @ 
% 2.58/2.82               (k6_relat_1 @ X31))
% 2.58/2.82          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 2.58/2.82          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 2.58/2.82          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 2.58/2.82          | ~ (v1_funct_1 @ X33))),
% 2.58/2.82      inference('demod', [status(thm)], ['63', '64'])).
% 2.58/2.82  thf('66', plain,
% 2.58/2.82      (![X0 : $i]:
% 2.58/2.82         (~ (v1_funct_1 @ X0)
% 2.58/2.82          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.58/2.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.58/2.82          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.58/2.82          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.58/2.82               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.58/2.82               (k6_relat_1 @ sk_A))
% 2.58/2.82          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.58/2.82          | ~ (v1_funct_1 @ sk_C))),
% 2.58/2.82      inference('sup-', [status(thm)], ['62', '65'])).
% 2.58/2.82  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('69', plain,
% 2.58/2.82      (![X0 : $i]:
% 2.58/2.82         (~ (v1_funct_1 @ X0)
% 2.58/2.82          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.58/2.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.58/2.82          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.58/2.82          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.58/2.82               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.58/2.82               (k6_relat_1 @ sk_A)))),
% 2.58/2.82      inference('demod', [status(thm)], ['66', '67', '68'])).
% 2.58/2.82  thf('70', plain,
% 2.58/2.82      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 2.58/2.82           (k6_relat_1 @ sk_A))
% 2.58/2.82        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.58/2.82        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.58/2.82        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.58/2.82        | ~ (v1_funct_1 @ sk_D))),
% 2.58/2.82      inference('sup-', [status(thm)], ['61', '69'])).
% 2.58/2.82  thf('71', plain,
% 2.58/2.82      (![X20 : $i]:
% 2.58/2.82         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 2.58/2.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 2.58/2.82      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.58/2.82  thf('72', plain,
% 2.58/2.82      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.58/2.82         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.58/2.82          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.58/2.82          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 2.58/2.82          | ((X16) != (X19)))),
% 2.58/2.82      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.58/2.82  thf('73', plain,
% 2.58/2.82      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.58/2.82         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 2.58/2.82          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.58/2.82      inference('simplify', [status(thm)], ['72'])).
% 2.58/2.82  thf('74', plain,
% 2.58/2.82      (![X0 : $i]:
% 2.58/2.82         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.58/2.82      inference('sup-', [status(thm)], ['71', '73'])).
% 2.58/2.82  thf('75', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf(redefinition_k2_relset_1, axiom,
% 2.58/2.82    (![A:$i,B:$i,C:$i]:
% 2.58/2.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.58/2.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.58/2.82  thf('76', plain,
% 2.58/2.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.58/2.82         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.58/2.82          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.58/2.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.58/2.82  thf('77', plain,
% 2.58/2.82      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.58/2.82      inference('sup-', [status(thm)], ['75', '76'])).
% 2.58/2.82  thf('78', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf('81', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.58/2.82      inference('demod', [status(thm)], ['70', '74', '77', '78', '79', '80'])).
% 2.58/2.82  thf(d3_funct_2, axiom,
% 2.58/2.82    (![A:$i,B:$i]:
% 2.58/2.82     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.58/2.82       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.58/2.82  thf('82', plain,
% 2.58/2.82      (![X21 : $i, X22 : $i]:
% 2.58/2.82         (((k2_relat_1 @ X22) != (X21))
% 2.58/2.82          | (v2_funct_2 @ X22 @ X21)
% 2.58/2.82          | ~ (v5_relat_1 @ X22 @ X21)
% 2.58/2.82          | ~ (v1_relat_1 @ X22))),
% 2.58/2.82      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.58/2.82  thf('83', plain,
% 2.58/2.82      (![X22 : $i]:
% 2.58/2.82         (~ (v1_relat_1 @ X22)
% 2.58/2.82          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 2.58/2.82          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 2.58/2.82      inference('simplify', [status(thm)], ['82'])).
% 2.58/2.82  thf('84', plain,
% 2.58/2.82      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.58/2.82        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.58/2.82        | ~ (v1_relat_1 @ sk_D))),
% 2.58/2.82      inference('sup-', [status(thm)], ['81', '83'])).
% 2.58/2.82  thf('85', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf(cc2_relset_1, axiom,
% 2.58/2.82    (![A:$i,B:$i,C:$i]:
% 2.58/2.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.58/2.82       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.58/2.82  thf('86', plain,
% 2.58/2.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.58/2.82         ((v5_relat_1 @ X10 @ X12)
% 2.58/2.82          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.58/2.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.58/2.82  thf('87', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.58/2.82      inference('sup-', [status(thm)], ['85', '86'])).
% 2.58/2.82  thf('88', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.58/2.82      inference('demod', [status(thm)], ['70', '74', '77', '78', '79', '80'])).
% 2.58/2.82  thf('89', plain,
% 2.58/2.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.58/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.58/2.82  thf(cc1_relset_1, axiom,
% 2.58/2.82    (![A:$i,B:$i,C:$i]:
% 2.58/2.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.58/2.82       ( v1_relat_1 @ C ) ))).
% 2.58/2.82  thf('90', plain,
% 2.58/2.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.58/2.82         ((v1_relat_1 @ X7)
% 2.58/2.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.58/2.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.58/2.82  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 2.58/2.82      inference('sup-', [status(thm)], ['89', '90'])).
% 2.58/2.82  thf('92', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.58/2.82      inference('demod', [status(thm)], ['84', '87', '88', '91'])).
% 2.58/2.82  thf('93', plain, ($false), inference('demod', [status(thm)], ['60', '92'])).
% 2.58/2.82  
% 2.58/2.82  % SZS output end Refutation
% 2.58/2.82  
% 2.58/2.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
