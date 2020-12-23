%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.45RiW4HEsv

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:22 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 294 expanded)
%              Number of leaves         :   40 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          : 1137 (5474 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('9',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
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
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('29',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
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
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
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
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != X24 )
      | ( v2_funct_2 @ X25 @ X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('78',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
      | ( v2_funct_2 @ X25 @ ( k2_relat_1 @ X25 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('87',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['79','82','83','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['57','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.45RiW4HEsv
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.77/3.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.77/3.98  % Solved by: fo/fo7.sh
% 3.77/3.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.77/3.98  % done 4466 iterations in 3.532s
% 3.77/3.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.77/3.98  % SZS output start Refutation
% 3.77/3.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.77/3.98  thf(sk_A_type, type, sk_A: $i).
% 3.77/3.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.77/3.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.77/3.98  thf(sk_D_type, type, sk_D: $i).
% 3.77/3.98  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.77/3.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.77/3.98  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.77/3.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.77/3.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.77/3.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.77/3.98  thf(sk_B_type, type, sk_B: $i).
% 3.77/3.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.77/3.98  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.77/3.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.77/3.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.77/3.98  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.77/3.98  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.77/3.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.77/3.98  thf(sk_C_type, type, sk_C: $i).
% 3.77/3.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.77/3.98  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.77/3.98  thf(t29_funct_2, conjecture,
% 3.77/3.98    (![A:$i,B:$i,C:$i]:
% 3.77/3.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.98       ( ![D:$i]:
% 3.77/3.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.77/3.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.77/3.98           ( ( r2_relset_1 @
% 3.77/3.98               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.77/3.98               ( k6_partfun1 @ A ) ) =>
% 3.77/3.98             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.77/3.98  thf(zf_stmt_0, negated_conjecture,
% 3.77/3.98    (~( ![A:$i,B:$i,C:$i]:
% 3.77/3.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.98            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.98          ( ![D:$i]:
% 3.77/3.98            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.77/3.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.77/3.98              ( ( r2_relset_1 @
% 3.77/3.98                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.77/3.98                  ( k6_partfun1 @ A ) ) =>
% 3.77/3.98                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.77/3.98    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.77/3.98  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('1', plain,
% 3.77/3.98      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.77/3.98      inference('split', [status(esa)], ['0'])).
% 3.77/3.98  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.77/3.98  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.77/3.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.77/3.98  thf(t8_boole, axiom,
% 3.77/3.98    (![A:$i,B:$i]:
% 3.77/3.98     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.77/3.98  thf('3', plain,
% 3.77/3.98      (![X0 : $i, X1 : $i]:
% 3.77/3.98         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.77/3.98      inference('cnf', [status(esa)], [t8_boole])).
% 3.77/3.98  thf('4', plain,
% 3.77/3.98      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.77/3.98      inference('sup-', [status(thm)], ['2', '3'])).
% 3.77/3.98  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.77/3.98  thf('5', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.77/3.98      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.77/3.98  thf(redefinition_k6_partfun1, axiom,
% 3.77/3.98    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.77/3.98  thf('6', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 3.77/3.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.98  thf('7', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.77/3.98      inference('demod', [status(thm)], ['5', '6'])).
% 3.77/3.98  thf(fc4_funct_1, axiom,
% 3.77/3.98    (![A:$i]:
% 3.77/3.98     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.77/3.98       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.77/3.98  thf('8', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 3.77/3.98      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.77/3.98  thf('9', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 3.77/3.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.98  thf('10', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 3.77/3.98      inference('demod', [status(thm)], ['8', '9'])).
% 3.77/3.98  thf('11', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.77/3.98      inference('sup+', [status(thm)], ['7', '10'])).
% 3.77/3.98  thf('12', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.77/3.98      inference('sup+', [status(thm)], ['4', '11'])).
% 3.77/3.98  thf('13', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.77/3.98      inference('split', [status(esa)], ['0'])).
% 3.77/3.98  thf('14', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.77/3.98      inference('sup-', [status(thm)], ['12', '13'])).
% 3.77/3.98  thf('15', plain,
% 3.77/3.98      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.77/3.98        (k6_partfun1 @ sk_A))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('16', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('17', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf(dt_k1_partfun1, axiom,
% 3.77/3.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.77/3.98     ( ( ( v1_funct_1 @ E ) & 
% 3.77/3.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.77/3.98         ( v1_funct_1 @ F ) & 
% 3.77/3.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.77/3.98       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.77/3.98         ( m1_subset_1 @
% 3.77/3.98           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.77/3.98           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.77/3.98  thf('18', plain,
% 3.77/3.98      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.77/3.98         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.77/3.98          | ~ (v1_funct_1 @ X26)
% 3.77/3.98          | ~ (v1_funct_1 @ X29)
% 3.77/3.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.77/3.98          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 3.77/3.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 3.77/3.98      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.77/3.98  thf('19', plain,
% 3.77/3.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.77/3.98         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.77/3.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.77/3.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.77/3.98          | ~ (v1_funct_1 @ X1)
% 3.77/3.98          | ~ (v1_funct_1 @ sk_C))),
% 3.77/3.98      inference('sup-', [status(thm)], ['17', '18'])).
% 3.77/3.98  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('21', plain,
% 3.77/3.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.77/3.98         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.77/3.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.77/3.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.77/3.98          | ~ (v1_funct_1 @ X1))),
% 3.77/3.98      inference('demod', [status(thm)], ['19', '20'])).
% 3.77/3.98  thf('22', plain,
% 3.77/3.98      ((~ (v1_funct_1 @ sk_D)
% 3.77/3.98        | (m1_subset_1 @ 
% 3.77/3.98           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.77/3.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.77/3.98      inference('sup-', [status(thm)], ['16', '21'])).
% 3.77/3.98  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('24', plain,
% 3.77/3.98      ((m1_subset_1 @ 
% 3.77/3.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.77/3.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.77/3.98      inference('demod', [status(thm)], ['22', '23'])).
% 3.77/3.98  thf(redefinition_r2_relset_1, axiom,
% 3.77/3.98    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.98     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.77/3.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.98       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.77/3.98  thf('25', plain,
% 3.77/3.98      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.98         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.77/3.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.77/3.98          | ((X19) = (X22))
% 3.77/3.98          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 3.77/3.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.77/3.98  thf('26', plain,
% 3.77/3.98      (![X0 : $i]:
% 3.77/3.98         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.98             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.77/3.98          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.77/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.77/3.98      inference('sup-', [status(thm)], ['24', '25'])).
% 3.77/3.98  thf('27', plain,
% 3.77/3.98      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.77/3.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.77/3.98        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.98            = (k6_partfun1 @ sk_A)))),
% 3.77/3.98      inference('sup-', [status(thm)], ['15', '26'])).
% 3.77/3.98  thf(t29_relset_1, axiom,
% 3.77/3.98    (![A:$i]:
% 3.77/3.98     ( m1_subset_1 @
% 3.77/3.98       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.77/3.98  thf('28', plain,
% 3.77/3.98      (![X23 : $i]:
% 3.77/3.98         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 3.77/3.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 3.77/3.98      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.77/3.98  thf('29', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 3.77/3.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.77/3.98  thf('30', plain,
% 3.77/3.98      (![X23 : $i]:
% 3.77/3.98         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 3.77/3.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 3.77/3.98      inference('demod', [status(thm)], ['28', '29'])).
% 3.77/3.98  thf('31', plain,
% 3.77/3.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.98         = (k6_partfun1 @ sk_A))),
% 3.77/3.98      inference('demod', [status(thm)], ['27', '30'])).
% 3.77/3.98  thf('32', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf(t26_funct_2, axiom,
% 3.77/3.98    (![A:$i,B:$i,C:$i,D:$i]:
% 3.77/3.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.77/3.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.98       ( ![E:$i]:
% 3.77/3.98         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.77/3.98             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.77/3.98           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.77/3.98             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.77/3.98               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.77/3.98  thf('33', plain,
% 3.77/3.98      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.77/3.98         (~ (v1_funct_1 @ X37)
% 3.77/3.98          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 3.77/3.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.77/3.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 3.77/3.98          | (v2_funct_1 @ X41)
% 3.77/3.98          | ((X39) = (k1_xboole_0))
% 3.77/3.98          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 3.77/3.98          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 3.77/3.98          | ~ (v1_funct_1 @ X41))),
% 3.77/3.98      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.77/3.98  thf('34', plain,
% 3.77/3.98      (![X0 : $i, X1 : $i]:
% 3.77/3.98         (~ (v1_funct_1 @ X0)
% 3.77/3.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.77/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.77/3.98          | ((sk_A) = (k1_xboole_0))
% 3.77/3.98          | (v2_funct_1 @ X0)
% 3.77/3.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.77/3.98          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.77/3.98          | ~ (v1_funct_1 @ sk_D))),
% 3.77/3.98      inference('sup-', [status(thm)], ['32', '33'])).
% 3.77/3.98  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('37', plain,
% 3.77/3.98      (![X0 : $i, X1 : $i]:
% 3.77/3.98         (~ (v1_funct_1 @ X0)
% 3.77/3.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.77/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.77/3.98          | ((sk_A) = (k1_xboole_0))
% 3.77/3.98          | (v2_funct_1 @ X0)
% 3.77/3.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.77/3.98      inference('demod', [status(thm)], ['34', '35', '36'])).
% 3.77/3.98  thf('38', plain,
% 3.77/3.98      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.77/3.98        | (v2_funct_1 @ sk_C)
% 3.77/3.98        | ((sk_A) = (k1_xboole_0))
% 3.77/3.98        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.77/3.98        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.77/3.98        | ~ (v1_funct_1 @ sk_C))),
% 3.77/3.98      inference('sup-', [status(thm)], ['31', '37'])).
% 3.77/3.98  thf('39', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 3.77/3.98      inference('demod', [status(thm)], ['8', '9'])).
% 3.77/3.98  thf('40', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('43', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.77/3.98      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 3.77/3.98  thf('44', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.77/3.98      inference('split', [status(esa)], ['0'])).
% 3.77/3.98  thf('45', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.77/3.98      inference('sup-', [status(thm)], ['43', '44'])).
% 3.77/3.98  thf('46', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf(cc1_subset_1, axiom,
% 3.77/3.98    (![A:$i]:
% 3.77/3.98     ( ( v1_xboole_0 @ A ) =>
% 3.77/3.98       ( ![B:$i]:
% 3.77/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.77/3.98  thf('47', plain,
% 3.77/3.98      (![X5 : $i, X6 : $i]:
% 3.77/3.98         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.77/3.98          | (v1_xboole_0 @ X5)
% 3.77/3.98          | ~ (v1_xboole_0 @ X6))),
% 3.77/3.98      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.77/3.98  thf('48', plain,
% 3.77/3.98      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.77/3.98      inference('sup-', [status(thm)], ['46', '47'])).
% 3.77/3.98  thf('49', plain,
% 3.77/3.98      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 3.77/3.98         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.77/3.98      inference('sup-', [status(thm)], ['45', '48'])).
% 3.77/3.98  thf(t113_zfmisc_1, axiom,
% 3.77/3.98    (![A:$i,B:$i]:
% 3.77/3.98     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.77/3.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.77/3.98  thf('50', plain,
% 3.77/3.98      (![X3 : $i, X4 : $i]:
% 3.77/3.98         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.77/3.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.77/3.98  thf('51', plain,
% 3.77/3.98      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.77/3.98      inference('simplify', [status(thm)], ['50'])).
% 3.77/3.98  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.77/3.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.77/3.98  thf('53', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.77/3.98      inference('demod', [status(thm)], ['49', '51', '52'])).
% 3.77/3.98  thf('54', plain, (((v2_funct_1 @ sk_C))),
% 3.77/3.98      inference('demod', [status(thm)], ['14', '53'])).
% 3.77/3.98  thf('55', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.77/3.98      inference('split', [status(esa)], ['0'])).
% 3.77/3.98  thf('56', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.77/3.98      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 3.77/3.98  thf('57', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.77/3.98      inference('simpl_trail', [status(thm)], ['1', '56'])).
% 3.77/3.98  thf('58', plain,
% 3.77/3.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.77/3.98         = (k6_partfun1 @ sk_A))),
% 3.77/3.98      inference('demod', [status(thm)], ['27', '30'])).
% 3.77/3.98  thf('59', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf(t24_funct_2, axiom,
% 3.77/3.98    (![A:$i,B:$i,C:$i]:
% 3.77/3.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.77/3.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.77/3.98       ( ![D:$i]:
% 3.77/3.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.77/3.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.77/3.98           ( ( r2_relset_1 @
% 3.77/3.98               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.77/3.98               ( k6_partfun1 @ B ) ) =>
% 3.77/3.98             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.77/3.98  thf('60', plain,
% 3.77/3.98      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.77/3.98         (~ (v1_funct_1 @ X33)
% 3.77/3.98          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 3.77/3.98          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.77/3.98          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 3.77/3.98               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 3.77/3.98               (k6_partfun1 @ X34))
% 3.77/3.98          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 3.77/3.98          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 3.77/3.98          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 3.77/3.98          | ~ (v1_funct_1 @ X36))),
% 3.77/3.98      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.77/3.98  thf('61', plain,
% 3.77/3.98      (![X0 : $i]:
% 3.77/3.98         (~ (v1_funct_1 @ X0)
% 3.77/3.98          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.77/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.77/3.98          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.77/3.98          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.98               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.77/3.98               (k6_partfun1 @ sk_A))
% 3.77/3.98          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.77/3.98          | ~ (v1_funct_1 @ sk_C))),
% 3.77/3.98      inference('sup-', [status(thm)], ['59', '60'])).
% 3.77/3.98  thf('62', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('64', plain,
% 3.77/3.98      (![X0 : $i]:
% 3.77/3.98         (~ (v1_funct_1 @ X0)
% 3.77/3.98          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.77/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.77/3.98          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.77/3.98          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.77/3.98               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.77/3.98               (k6_partfun1 @ sk_A)))),
% 3.77/3.98      inference('demod', [status(thm)], ['61', '62', '63'])).
% 3.77/3.98  thf('65', plain,
% 3.77/3.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 3.77/3.98           (k6_partfun1 @ sk_A))
% 3.77/3.98        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.77/3.98        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.77/3.98        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.77/3.98        | ~ (v1_funct_1 @ sk_D))),
% 3.77/3.98      inference('sup-', [status(thm)], ['58', '64'])).
% 3.77/3.98  thf('66', plain,
% 3.77/3.98      (![X23 : $i]:
% 3.77/3.98         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 3.77/3.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 3.77/3.98      inference('demod', [status(thm)], ['28', '29'])).
% 3.77/3.98  thf('67', plain,
% 3.77/3.98      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.98         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.77/3.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.77/3.98          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 3.77/3.98          | ((X19) != (X22)))),
% 3.77/3.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.77/3.98  thf('68', plain,
% 3.77/3.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.77/3.98         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 3.77/3.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.77/3.98      inference('simplify', [status(thm)], ['67'])).
% 3.77/3.98  thf('69', plain,
% 3.77/3.98      (![X0 : $i]:
% 3.77/3.98         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 3.77/3.98      inference('sup-', [status(thm)], ['66', '68'])).
% 3.77/3.98  thf('70', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf(redefinition_k2_relset_1, axiom,
% 3.77/3.98    (![A:$i,B:$i,C:$i]:
% 3.77/3.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.77/3.98  thf('71', plain,
% 3.77/3.98      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.77/3.98         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 3.77/3.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.77/3.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.77/3.98  thf('72', plain,
% 3.77/3.98      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.77/3.98      inference('sup-', [status(thm)], ['70', '71'])).
% 3.77/3.98  thf('73', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf('76', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.77/3.98      inference('demod', [status(thm)], ['65', '69', '72', '73', '74', '75'])).
% 3.77/3.98  thf(d3_funct_2, axiom,
% 3.77/3.98    (![A:$i,B:$i]:
% 3.77/3.98     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.77/3.98       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.77/3.98  thf('77', plain,
% 3.77/3.98      (![X24 : $i, X25 : $i]:
% 3.77/3.98         (((k2_relat_1 @ X25) != (X24))
% 3.77/3.98          | (v2_funct_2 @ X25 @ X24)
% 3.77/3.98          | ~ (v5_relat_1 @ X25 @ X24)
% 3.77/3.98          | ~ (v1_relat_1 @ X25))),
% 3.77/3.98      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.77/3.98  thf('78', plain,
% 3.77/3.98      (![X25 : $i]:
% 3.77/3.98         (~ (v1_relat_1 @ X25)
% 3.77/3.98          | ~ (v5_relat_1 @ X25 @ (k2_relat_1 @ X25))
% 3.77/3.98          | (v2_funct_2 @ X25 @ (k2_relat_1 @ X25)))),
% 3.77/3.98      inference('simplify', [status(thm)], ['77'])).
% 3.77/3.98  thf('79', plain,
% 3.77/3.98      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.77/3.98        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.77/3.98        | ~ (v1_relat_1 @ sk_D))),
% 3.77/3.98      inference('sup-', [status(thm)], ['76', '78'])).
% 3.77/3.98  thf('80', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf(cc2_relset_1, axiom,
% 3.77/3.98    (![A:$i,B:$i,C:$i]:
% 3.77/3.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.77/3.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.77/3.98  thf('81', plain,
% 3.77/3.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.77/3.98         ((v5_relat_1 @ X13 @ X15)
% 3.77/3.98          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.77/3.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.77/3.98  thf('82', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.77/3.98      inference('sup-', [status(thm)], ['80', '81'])).
% 3.77/3.98  thf('83', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.77/3.98      inference('demod', [status(thm)], ['65', '69', '72', '73', '74', '75'])).
% 3.77/3.98  thf('84', plain,
% 3.77/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.77/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.77/3.98  thf(cc2_relat_1, axiom,
% 3.77/3.98    (![A:$i]:
% 3.77/3.98     ( ( v1_relat_1 @ A ) =>
% 3.77/3.98       ( ![B:$i]:
% 3.77/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.77/3.98  thf('85', plain,
% 3.77/3.98      (![X7 : $i, X8 : $i]:
% 3.77/3.98         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 3.77/3.98          | (v1_relat_1 @ X7)
% 3.77/3.98          | ~ (v1_relat_1 @ X8))),
% 3.77/3.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.77/3.98  thf('86', plain,
% 3.77/3.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.77/3.98      inference('sup-', [status(thm)], ['84', '85'])).
% 3.77/3.98  thf(fc6_relat_1, axiom,
% 3.77/3.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.77/3.98  thf('87', plain,
% 3.77/3.98      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 3.77/3.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.77/3.98  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 3.77/3.98      inference('demod', [status(thm)], ['86', '87'])).
% 3.77/3.98  thf('89', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.77/3.98      inference('demod', [status(thm)], ['79', '82', '83', '88'])).
% 3.77/3.98  thf('90', plain, ($false), inference('demod', [status(thm)], ['57', '89'])).
% 3.77/3.98  
% 3.77/3.98  % SZS output end Refutation
% 3.77/3.98  
% 3.77/3.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
