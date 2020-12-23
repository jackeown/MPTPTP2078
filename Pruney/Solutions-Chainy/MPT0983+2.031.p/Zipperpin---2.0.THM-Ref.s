%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FoPhwjPQgN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:05 EST 2020

% Result     : Theorem 2.85s
% Output     : Refutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 291 expanded)
%              Number of leaves         :   39 ( 101 expanded)
%              Depth                    :   18
%              Number of atoms          : 1120 (5454 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('5',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('9',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('28',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('29',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35 ) )
      | ( v2_funct_1 @ X39 )
      | ( X37 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','51','52'])).

thf('54',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['14','53'])).

thf('55',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','56'])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('68',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['65','69','72','73','74','75'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('77',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('78',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('81',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['65','69','72','73','74','75'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('85',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['79','82','83','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['57','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FoPhwjPQgN
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.85/3.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.85/3.05  % Solved by: fo/fo7.sh
% 2.85/3.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.85/3.05  % done 3516 iterations in 2.607s
% 2.85/3.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.85/3.05  % SZS output start Refutation
% 2.85/3.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.85/3.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.85/3.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.85/3.05  thf(sk_C_type, type, sk_C: $i).
% 2.85/3.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.85/3.05  thf(sk_B_type, type, sk_B: $i).
% 2.85/3.05  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.85/3.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.85/3.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.85/3.05  thf(sk_D_type, type, sk_D: $i).
% 2.85/3.05  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.85/3.05  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.85/3.05  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.85/3.05  thf(sk_A_type, type, sk_A: $i).
% 2.85/3.05  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.85/3.05  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.85/3.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.85/3.05  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.85/3.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.85/3.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.85/3.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.85/3.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.85/3.05  thf(t29_funct_2, conjecture,
% 2.85/3.05    (![A:$i,B:$i,C:$i]:
% 2.85/3.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.85/3.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.85/3.05       ( ![D:$i]:
% 2.85/3.05         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.85/3.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.85/3.05           ( ( r2_relset_1 @
% 2.85/3.05               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.85/3.05               ( k6_partfun1 @ A ) ) =>
% 2.85/3.05             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.85/3.05  thf(zf_stmt_0, negated_conjecture,
% 2.85/3.05    (~( ![A:$i,B:$i,C:$i]:
% 2.85/3.05        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.85/3.05            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.85/3.05          ( ![D:$i]:
% 2.85/3.05            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.85/3.05                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.85/3.05              ( ( r2_relset_1 @
% 2.85/3.05                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.85/3.05                  ( k6_partfun1 @ A ) ) =>
% 2.85/3.05                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.85/3.05    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.85/3.05  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.85/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.05  thf('1', plain,
% 2.85/3.05      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.85/3.05      inference('split', [status(esa)], ['0'])).
% 2.85/3.05  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.85/3.05  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.85/3.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.85/3.05  thf(t8_boole, axiom,
% 2.85/3.05    (![A:$i,B:$i]:
% 2.85/3.05     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.85/3.05  thf('3', plain,
% 2.85/3.05      (![X0 : $i, X1 : $i]:
% 2.85/3.05         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.85/3.05      inference('cnf', [status(esa)], [t8_boole])).
% 2.85/3.05  thf('4', plain,
% 2.85/3.05      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.85/3.05      inference('sup-', [status(thm)], ['2', '3'])).
% 2.85/3.05  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.85/3.05  thf('5', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.85/3.05      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.85/3.05  thf(redefinition_k6_partfun1, axiom,
% 2.85/3.05    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.85/3.05  thf('6', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.85/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.85/3.05  thf('7', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.85/3.05      inference('demod', [status(thm)], ['5', '6'])).
% 2.85/3.05  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.85/3.05  thf('8', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 2.85/3.05      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.85/3.05  thf('9', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.85/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.85/3.05  thf('10', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 2.85/3.05      inference('demod', [status(thm)], ['8', '9'])).
% 2.85/3.05  thf('11', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.85/3.05      inference('sup+', [status(thm)], ['7', '10'])).
% 2.85/3.05  thf('12', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.85/3.05      inference('sup+', [status(thm)], ['4', '11'])).
% 2.85/3.05  thf('13', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.85/3.05      inference('split', [status(esa)], ['0'])).
% 2.85/3.05  thf('14', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.85/3.05      inference('sup-', [status(thm)], ['12', '13'])).
% 2.85/3.05  thf('15', plain,
% 2.85/3.05      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.85/3.05        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.85/3.05        (k6_partfun1 @ sk_A))),
% 2.85/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.05  thf('16', plain,
% 2.85/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.85/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.05  thf('17', plain,
% 2.85/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.85/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.05  thf(dt_k1_partfun1, axiom,
% 2.85/3.05    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.85/3.05     ( ( ( v1_funct_1 @ E ) & 
% 2.85/3.05         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.85/3.05         ( v1_funct_1 @ F ) & 
% 2.85/3.05         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.85/3.05       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.85/3.05         ( m1_subset_1 @
% 2.85/3.05           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.85/3.05           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.85/3.05  thf('18', plain,
% 2.85/3.05      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.85/3.05         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.85/3.05          | ~ (v1_funct_1 @ X24)
% 2.85/3.05          | ~ (v1_funct_1 @ X27)
% 2.85/3.05          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.85/3.06          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 2.85/3.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 2.85/3.06      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.85/3.06  thf('19', plain,
% 2.85/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.85/3.06         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.85/3.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.85/3.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.85/3.06          | ~ (v1_funct_1 @ X1)
% 2.85/3.06          | ~ (v1_funct_1 @ sk_C))),
% 2.85/3.06      inference('sup-', [status(thm)], ['17', '18'])).
% 2.85/3.06  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('21', plain,
% 2.85/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.85/3.06         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.85/3.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.85/3.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.85/3.06          | ~ (v1_funct_1 @ X1))),
% 2.85/3.06      inference('demod', [status(thm)], ['19', '20'])).
% 2.85/3.06  thf('22', plain,
% 2.85/3.06      ((~ (v1_funct_1 @ sk_D)
% 2.85/3.06        | (m1_subset_1 @ 
% 2.85/3.06           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.85/3.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.85/3.06      inference('sup-', [status(thm)], ['16', '21'])).
% 2.85/3.06  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('24', plain,
% 2.85/3.06      ((m1_subset_1 @ 
% 2.85/3.06        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.85/3.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.85/3.06      inference('demod', [status(thm)], ['22', '23'])).
% 2.85/3.06  thf(redefinition_r2_relset_1, axiom,
% 2.85/3.06    (![A:$i,B:$i,C:$i,D:$i]:
% 2.85/3.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.85/3.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.85/3.06       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.85/3.06  thf('25', plain,
% 2.85/3.06      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.85/3.06         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.85/3.06          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.85/3.06          | ((X17) = (X20))
% 2.85/3.06          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 2.85/3.06      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.85/3.06  thf('26', plain,
% 2.85/3.06      (![X0 : $i]:
% 2.85/3.06         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.85/3.06             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.85/3.06          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.85/3.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.85/3.06      inference('sup-', [status(thm)], ['24', '25'])).
% 2.85/3.06  thf('27', plain,
% 2.85/3.06      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.85/3.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.85/3.06        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.85/3.06            = (k6_partfun1 @ sk_A)))),
% 2.85/3.06      inference('sup-', [status(thm)], ['15', '26'])).
% 2.85/3.06  thf(t29_relset_1, axiom,
% 2.85/3.06    (![A:$i]:
% 2.85/3.06     ( m1_subset_1 @
% 2.85/3.06       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.85/3.06  thf('28', plain,
% 2.85/3.06      (![X21 : $i]:
% 2.85/3.06         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 2.85/3.06          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 2.85/3.06      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.85/3.06  thf('29', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.85/3.06      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.85/3.06  thf('30', plain,
% 2.85/3.06      (![X21 : $i]:
% 2.85/3.06         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 2.85/3.06          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 2.85/3.06      inference('demod', [status(thm)], ['28', '29'])).
% 2.85/3.06  thf('31', plain,
% 2.85/3.06      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.85/3.06         = (k6_partfun1 @ sk_A))),
% 2.85/3.06      inference('demod', [status(thm)], ['27', '30'])).
% 2.85/3.06  thf('32', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf(t26_funct_2, axiom,
% 2.85/3.06    (![A:$i,B:$i,C:$i,D:$i]:
% 2.85/3.06     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.85/3.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.85/3.06       ( ![E:$i]:
% 2.85/3.06         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.85/3.06             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.85/3.06           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.85/3.06             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.85/3.06               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.85/3.06  thf('33', plain,
% 2.85/3.06      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.85/3.06         (~ (v1_funct_1 @ X35)
% 2.85/3.06          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 2.85/3.06          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.85/3.06          | ~ (v2_funct_1 @ (k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35))
% 2.85/3.06          | (v2_funct_1 @ X39)
% 2.85/3.06          | ((X37) = (k1_xboole_0))
% 2.85/3.06          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 2.85/3.06          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 2.85/3.06          | ~ (v1_funct_1 @ X39))),
% 2.85/3.06      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.85/3.06  thf('34', plain,
% 2.85/3.06      (![X0 : $i, X1 : $i]:
% 2.85/3.06         (~ (v1_funct_1 @ X0)
% 2.85/3.06          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.85/3.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.85/3.06          | ((sk_A) = (k1_xboole_0))
% 2.85/3.06          | (v2_funct_1 @ X0)
% 2.85/3.06          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.85/3.06          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.85/3.06          | ~ (v1_funct_1 @ sk_D))),
% 2.85/3.06      inference('sup-', [status(thm)], ['32', '33'])).
% 2.85/3.06  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('37', plain,
% 2.85/3.06      (![X0 : $i, X1 : $i]:
% 2.85/3.06         (~ (v1_funct_1 @ X0)
% 2.85/3.06          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.85/3.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.85/3.06          | ((sk_A) = (k1_xboole_0))
% 2.85/3.06          | (v2_funct_1 @ X0)
% 2.85/3.06          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.85/3.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 2.85/3.06  thf('38', plain,
% 2.85/3.06      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.85/3.06        | (v2_funct_1 @ sk_C)
% 2.85/3.06        | ((sk_A) = (k1_xboole_0))
% 2.85/3.06        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.85/3.06        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.85/3.06        | ~ (v1_funct_1 @ sk_C))),
% 2.85/3.06      inference('sup-', [status(thm)], ['31', '37'])).
% 2.85/3.06  thf('39', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 2.85/3.06      inference('demod', [status(thm)], ['8', '9'])).
% 2.85/3.06  thf('40', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('43', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.85/3.06      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 2.85/3.06  thf('44', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.85/3.06      inference('split', [status(esa)], ['0'])).
% 2.85/3.06  thf('45', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.85/3.06      inference('sup-', [status(thm)], ['43', '44'])).
% 2.85/3.06  thf('46', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf(cc1_subset_1, axiom,
% 2.85/3.06    (![A:$i]:
% 2.85/3.06     ( ( v1_xboole_0 @ A ) =>
% 2.85/3.06       ( ![B:$i]:
% 2.85/3.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 2.85/3.06  thf('47', plain,
% 2.85/3.06      (![X5 : $i, X6 : $i]:
% 2.85/3.06         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.85/3.06          | (v1_xboole_0 @ X5)
% 2.85/3.06          | ~ (v1_xboole_0 @ X6))),
% 2.85/3.06      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.85/3.06  thf('48', plain,
% 2.85/3.06      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 2.85/3.06      inference('sup-', [status(thm)], ['46', '47'])).
% 2.85/3.06  thf('49', plain,
% 2.85/3.06      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 2.85/3.06         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.85/3.06      inference('sup-', [status(thm)], ['45', '48'])).
% 2.85/3.06  thf(t113_zfmisc_1, axiom,
% 2.85/3.06    (![A:$i,B:$i]:
% 2.85/3.06     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.85/3.06       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.85/3.06  thf('50', plain,
% 2.85/3.06      (![X3 : $i, X4 : $i]:
% 2.85/3.06         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.85/3.06      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.85/3.06  thf('51', plain,
% 2.85/3.06      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.85/3.06      inference('simplify', [status(thm)], ['50'])).
% 2.85/3.06  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.85/3.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.85/3.06  thf('53', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.85/3.06      inference('demod', [status(thm)], ['49', '51', '52'])).
% 2.85/3.06  thf('54', plain, (((v2_funct_1 @ sk_C))),
% 2.85/3.06      inference('demod', [status(thm)], ['14', '53'])).
% 2.85/3.06  thf('55', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 2.85/3.06      inference('split', [status(esa)], ['0'])).
% 2.85/3.06  thf('56', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.85/3.06      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 2.85/3.06  thf('57', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 2.85/3.06      inference('simpl_trail', [status(thm)], ['1', '56'])).
% 2.85/3.06  thf('58', plain,
% 2.85/3.06      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.85/3.06         = (k6_partfun1 @ sk_A))),
% 2.85/3.06      inference('demod', [status(thm)], ['27', '30'])).
% 2.85/3.06  thf('59', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf(t24_funct_2, axiom,
% 2.85/3.06    (![A:$i,B:$i,C:$i]:
% 2.85/3.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.85/3.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.85/3.06       ( ![D:$i]:
% 2.85/3.06         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.85/3.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.85/3.06           ( ( r2_relset_1 @
% 2.85/3.06               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.85/3.06               ( k6_partfun1 @ B ) ) =>
% 2.85/3.06             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.85/3.06  thf('60', plain,
% 2.85/3.06      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.85/3.06         (~ (v1_funct_1 @ X31)
% 2.85/3.06          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 2.85/3.06          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.85/3.06          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 2.85/3.06               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 2.85/3.06               (k6_partfun1 @ X32))
% 2.85/3.06          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 2.85/3.06          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 2.85/3.06          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 2.85/3.06          | ~ (v1_funct_1 @ X34))),
% 2.85/3.06      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.85/3.06  thf('61', plain,
% 2.85/3.06      (![X0 : $i]:
% 2.85/3.06         (~ (v1_funct_1 @ X0)
% 2.85/3.06          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.85/3.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.85/3.06          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.85/3.06          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.85/3.06               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.85/3.06               (k6_partfun1 @ sk_A))
% 2.85/3.06          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.85/3.06          | ~ (v1_funct_1 @ sk_C))),
% 2.85/3.06      inference('sup-', [status(thm)], ['59', '60'])).
% 2.85/3.06  thf('62', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('64', plain,
% 2.85/3.06      (![X0 : $i]:
% 2.85/3.06         (~ (v1_funct_1 @ X0)
% 2.85/3.06          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.85/3.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.85/3.06          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.85/3.06          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.85/3.06               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.85/3.06               (k6_partfun1 @ sk_A)))),
% 2.85/3.06      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.85/3.06  thf('65', plain,
% 2.85/3.06      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 2.85/3.06           (k6_partfun1 @ sk_A))
% 2.85/3.06        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.85/3.06        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.85/3.06        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.85/3.06        | ~ (v1_funct_1 @ sk_D))),
% 2.85/3.06      inference('sup-', [status(thm)], ['58', '64'])).
% 2.85/3.06  thf('66', plain,
% 2.85/3.06      (![X21 : $i]:
% 2.85/3.06         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 2.85/3.06          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 2.85/3.06      inference('demod', [status(thm)], ['28', '29'])).
% 2.85/3.06  thf('67', plain,
% 2.85/3.06      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.85/3.06         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.85/3.06          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.85/3.06          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 2.85/3.06          | ((X17) != (X20)))),
% 2.85/3.06      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.85/3.06  thf('68', plain,
% 2.85/3.06      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.85/3.06         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 2.85/3.06          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.85/3.06      inference('simplify', [status(thm)], ['67'])).
% 2.85/3.06  thf('69', plain,
% 2.85/3.06      (![X0 : $i]:
% 2.85/3.06         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 2.85/3.06      inference('sup-', [status(thm)], ['66', '68'])).
% 2.85/3.06  thf('70', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf(redefinition_k2_relset_1, axiom,
% 2.85/3.06    (![A:$i,B:$i,C:$i]:
% 2.85/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.85/3.06       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.85/3.06  thf('71', plain,
% 2.85/3.06      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.85/3.06         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 2.85/3.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.85/3.06      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.85/3.06  thf('72', plain,
% 2.85/3.06      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.85/3.06      inference('sup-', [status(thm)], ['70', '71'])).
% 2.85/3.06  thf('73', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf('76', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.85/3.06      inference('demod', [status(thm)], ['65', '69', '72', '73', '74', '75'])).
% 2.85/3.06  thf(d3_funct_2, axiom,
% 2.85/3.06    (![A:$i,B:$i]:
% 2.85/3.06     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.85/3.06       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.85/3.06  thf('77', plain,
% 2.85/3.06      (![X22 : $i, X23 : $i]:
% 2.85/3.06         (((k2_relat_1 @ X23) != (X22))
% 2.85/3.06          | (v2_funct_2 @ X23 @ X22)
% 2.85/3.06          | ~ (v5_relat_1 @ X23 @ X22)
% 2.85/3.06          | ~ (v1_relat_1 @ X23))),
% 2.85/3.06      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.85/3.06  thf('78', plain,
% 2.85/3.06      (![X23 : $i]:
% 2.85/3.06         (~ (v1_relat_1 @ X23)
% 2.85/3.06          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 2.85/3.06          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 2.85/3.06      inference('simplify', [status(thm)], ['77'])).
% 2.85/3.06  thf('79', plain,
% 2.85/3.06      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.85/3.06        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.85/3.06        | ~ (v1_relat_1 @ sk_D))),
% 2.85/3.06      inference('sup-', [status(thm)], ['76', '78'])).
% 2.85/3.06  thf('80', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf(cc2_relset_1, axiom,
% 2.85/3.06    (![A:$i,B:$i,C:$i]:
% 2.85/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.85/3.06       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.85/3.06  thf('81', plain,
% 2.85/3.06      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.85/3.06         ((v5_relat_1 @ X11 @ X13)
% 2.85/3.06          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.85/3.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.85/3.06  thf('82', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.85/3.06      inference('sup-', [status(thm)], ['80', '81'])).
% 2.85/3.06  thf('83', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.85/3.06      inference('demod', [status(thm)], ['65', '69', '72', '73', '74', '75'])).
% 2.85/3.06  thf('84', plain,
% 2.85/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.85/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.85/3.06  thf(cc1_relset_1, axiom,
% 2.85/3.06    (![A:$i,B:$i,C:$i]:
% 2.85/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.85/3.06       ( v1_relat_1 @ C ) ))).
% 2.85/3.06  thf('85', plain,
% 2.85/3.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.85/3.06         ((v1_relat_1 @ X8)
% 2.85/3.06          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 2.85/3.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.85/3.06  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 2.85/3.06      inference('sup-', [status(thm)], ['84', '85'])).
% 2.85/3.06  thf('87', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.85/3.06      inference('demod', [status(thm)], ['79', '82', '83', '86'])).
% 2.85/3.06  thf('88', plain, ($false), inference('demod', [status(thm)], ['57', '87'])).
% 2.85/3.06  
% 2.85/3.06  % SZS output end Refutation
% 2.85/3.06  
% 2.85/3.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
