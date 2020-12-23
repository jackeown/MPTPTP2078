%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZVRAaKshxc

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:20 EST 2020

% Result     : Theorem 6.81s
% Output     : Refutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 494 expanded)
%              Number of leaves         :   45 ( 162 expanded)
%              Depth                    :   20
%              Number of atoms          : 1173 (8495 expanded)
%              Number of equality atoms :   51 ( 127 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
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
    ! [X21: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X21: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X21 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('35',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('36',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21','38'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('44',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('46',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21','38'])).

thf('59',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','57','58','59','60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('71',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ X31 )
       != X30 )
      | ( v2_funct_2 @ X31 @ X30 )
      | ~ ( v5_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('72',plain,(
    ! [X31: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v5_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
      | ( v2_funct_2 @ X31 @ ( k2_relat_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['66','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('77',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('79',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['13','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45 ) )
      | ( v2_funct_1 @ X49 )
      | ( X47 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X46 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X21: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X21 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('100',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('101',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['98','101'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('104',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['85','102','104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['82','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZVRAaKshxc
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.81/6.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.81/6.99  % Solved by: fo/fo7.sh
% 6.81/6.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.81/6.99  % done 7077 iterations in 6.528s
% 6.81/6.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.81/6.99  % SZS output start Refutation
% 6.81/6.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.81/6.99  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.81/6.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.81/6.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.81/6.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.81/6.99  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.81/6.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.81/6.99  thf(sk_A_type, type, sk_A: $i).
% 6.81/6.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.81/6.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.81/6.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.81/6.99  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.81/6.99  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 6.81/6.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.81/6.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.81/6.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.81/6.99  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.81/6.99  thf(sk_D_type, type, sk_D: $i).
% 6.81/6.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.81/6.99  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.81/6.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.81/6.99  thf(sk_C_type, type, sk_C: $i).
% 6.81/6.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.81/6.99  thf(sk_B_type, type, sk_B: $i).
% 6.81/6.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.81/6.99  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.81/6.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.81/6.99  thf(t8_boole, axiom,
% 6.81/6.99    (![A:$i,B:$i]:
% 6.81/6.99     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 6.81/6.99  thf('1', plain,
% 6.81/6.99      (![X3 : $i, X4 : $i]:
% 6.81/6.99         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 6.81/6.99      inference('cnf', [status(esa)], [t8_boole])).
% 6.81/6.99  thf('2', plain,
% 6.81/6.99      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.81/6.99      inference('sup-', [status(thm)], ['0', '1'])).
% 6.81/6.99  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 6.81/6.99  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.81/6.99      inference('cnf', [status(esa)], [t81_relat_1])).
% 6.81/6.99  thf(redefinition_k6_partfun1, axiom,
% 6.81/6.99    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.81/6.99  thf('4', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 6.81/6.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.81/6.99  thf('5', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.81/6.99      inference('demod', [status(thm)], ['3', '4'])).
% 6.81/6.99  thf(fc4_funct_1, axiom,
% 6.81/6.99    (![A:$i]:
% 6.81/6.99     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 6.81/6.99       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 6.81/6.99  thf('6', plain, (![X21 : $i]: (v2_funct_1 @ (k6_relat_1 @ X21))),
% 6.81/6.99      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.81/6.99  thf('7', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 6.81/6.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.81/6.99  thf('8', plain, (![X21 : $i]: (v2_funct_1 @ (k6_partfun1 @ X21))),
% 6.81/6.99      inference('demod', [status(thm)], ['6', '7'])).
% 6.81/6.99  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 6.81/6.99      inference('sup+', [status(thm)], ['5', '8'])).
% 6.81/6.99  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 6.81/6.99      inference('sup+', [status(thm)], ['2', '9'])).
% 6.81/6.99  thf(t29_funct_2, conjecture,
% 6.81/6.99    (![A:$i,B:$i,C:$i]:
% 6.81/6.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.81/6.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.81/6.99       ( ![D:$i]:
% 6.81/6.99         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.81/6.99             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.81/6.99           ( ( r2_relset_1 @
% 6.81/6.99               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.81/6.99               ( k6_partfun1 @ A ) ) =>
% 6.81/6.99             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 6.81/6.99  thf(zf_stmt_0, negated_conjecture,
% 6.81/6.99    (~( ![A:$i,B:$i,C:$i]:
% 6.81/6.99        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.81/6.99            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.81/6.99          ( ![D:$i]:
% 6.81/6.99            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.81/6.99                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.81/6.99              ( ( r2_relset_1 @
% 6.81/6.99                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.81/6.99                  ( k6_partfun1 @ A ) ) =>
% 6.81/6.99                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 6.81/6.99    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 6.81/6.99  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.81/6.99      inference('split', [status(esa)], ['11'])).
% 6.81/6.99  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.81/6.99      inference('sup-', [status(thm)], ['10', '12'])).
% 6.81/6.99  thf('14', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('15', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf(redefinition_k1_partfun1, axiom,
% 6.81/6.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.81/6.99     ( ( ( v1_funct_1 @ E ) & 
% 6.81/6.99         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.81/6.99         ( v1_funct_1 @ F ) & 
% 6.81/6.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.81/6.99       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.81/6.99  thf('16', plain,
% 6.81/6.99      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 6.81/6.99         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 6.81/6.99          | ~ (v1_funct_1 @ X38)
% 6.81/6.99          | ~ (v1_funct_1 @ X41)
% 6.81/6.99          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 6.81/6.99          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 6.81/6.99              = (k5_relat_1 @ X38 @ X41)))),
% 6.81/6.99      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.81/6.99  thf('17', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.81/6.99         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.81/6.99            = (k5_relat_1 @ sk_C @ X0))
% 6.81/6.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.81/6.99          | ~ (v1_funct_1 @ X0)
% 6.81/6.99          | ~ (v1_funct_1 @ sk_C))),
% 6.81/6.99      inference('sup-', [status(thm)], ['15', '16'])).
% 6.81/6.99  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('19', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.81/6.99         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.81/6.99            = (k5_relat_1 @ sk_C @ X0))
% 6.81/6.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.81/6.99          | ~ (v1_funct_1 @ X0))),
% 6.81/6.99      inference('demod', [status(thm)], ['17', '18'])).
% 6.81/6.99  thf('20', plain,
% 6.81/6.99      ((~ (v1_funct_1 @ sk_D)
% 6.81/6.99        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.81/6.99            = (k5_relat_1 @ sk_C @ sk_D)))),
% 6.81/6.99      inference('sup-', [status(thm)], ['14', '19'])).
% 6.81/6.99  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('22', plain,
% 6.81/6.99      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.81/6.99        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.81/6.99        (k6_partfun1 @ sk_A))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('23', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('24', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf(dt_k1_partfun1, axiom,
% 6.81/6.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.81/6.99     ( ( ( v1_funct_1 @ E ) & 
% 6.81/6.99         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.81/6.99         ( v1_funct_1 @ F ) & 
% 6.81/6.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.81/6.99       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.81/6.99         ( m1_subset_1 @
% 6.81/6.99           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.81/6.99           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.81/6.99  thf('25', plain,
% 6.81/6.99      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 6.81/6.99         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 6.81/6.99          | ~ (v1_funct_1 @ X32)
% 6.81/6.99          | ~ (v1_funct_1 @ X35)
% 6.81/6.99          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.81/6.99          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 6.81/6.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 6.81/6.99      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.81/6.99  thf('26', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.81/6.99         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.81/6.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.81/6.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.81/6.99          | ~ (v1_funct_1 @ X1)
% 6.81/6.99          | ~ (v1_funct_1 @ sk_C))),
% 6.81/6.99      inference('sup-', [status(thm)], ['24', '25'])).
% 6.81/6.99  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('28', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.81/6.99         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.81/6.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.81/6.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.81/6.99          | ~ (v1_funct_1 @ X1))),
% 6.81/6.99      inference('demod', [status(thm)], ['26', '27'])).
% 6.81/6.99  thf('29', plain,
% 6.81/6.99      ((~ (v1_funct_1 @ sk_D)
% 6.81/6.99        | (m1_subset_1 @ 
% 6.81/6.99           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.81/6.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.81/6.99      inference('sup-', [status(thm)], ['23', '28'])).
% 6.81/6.99  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('31', plain,
% 6.81/6.99      ((m1_subset_1 @ 
% 6.81/6.99        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.81/6.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.81/6.99      inference('demod', [status(thm)], ['29', '30'])).
% 6.81/6.99  thf(redefinition_r2_relset_1, axiom,
% 6.81/6.99    (![A:$i,B:$i,C:$i,D:$i]:
% 6.81/6.99     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.81/6.99         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.81/6.99       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.81/6.99  thf('32', plain,
% 6.81/6.99      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 6.81/6.99         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 6.81/6.99          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 6.81/6.99          | ((X25) = (X28))
% 6.81/6.99          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 6.81/6.99      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.81/6.99  thf('33', plain,
% 6.81/6.99      (![X0 : $i]:
% 6.81/6.99         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.81/6.99             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 6.81/6.99          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 6.81/6.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.81/6.99      inference('sup-', [status(thm)], ['31', '32'])).
% 6.81/6.99  thf('34', plain,
% 6.81/6.99      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 6.81/6.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.81/6.99        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.81/6.99            = (k6_partfun1 @ sk_A)))),
% 6.81/6.99      inference('sup-', [status(thm)], ['22', '33'])).
% 6.81/6.99  thf(t29_relset_1, axiom,
% 6.81/6.99    (![A:$i]:
% 6.81/6.99     ( m1_subset_1 @
% 6.81/6.99       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 6.81/6.99  thf('35', plain,
% 6.81/6.99      (![X29 : $i]:
% 6.81/6.99         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 6.81/6.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 6.81/6.99      inference('cnf', [status(esa)], [t29_relset_1])).
% 6.81/6.99  thf('36', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 6.81/6.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.81/6.99  thf('37', plain,
% 6.81/6.99      (![X29 : $i]:
% 6.81/6.99         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 6.81/6.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 6.81/6.99      inference('demod', [status(thm)], ['35', '36'])).
% 6.81/6.99  thf('38', plain,
% 6.81/6.99      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.81/6.99         = (k6_partfun1 @ sk_A))),
% 6.81/6.99      inference('demod', [status(thm)], ['34', '37'])).
% 6.81/6.99  thf('39', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 6.81/6.99      inference('demod', [status(thm)], ['20', '21', '38'])).
% 6.81/6.99  thf(t45_relat_1, axiom,
% 6.81/6.99    (![A:$i]:
% 6.81/6.99     ( ( v1_relat_1 @ A ) =>
% 6.81/6.99       ( ![B:$i]:
% 6.81/6.99         ( ( v1_relat_1 @ B ) =>
% 6.81/6.99           ( r1_tarski @
% 6.81/6.99             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 6.81/6.99  thf('40', plain,
% 6.81/6.99      (![X16 : $i, X17 : $i]:
% 6.81/6.99         (~ (v1_relat_1 @ X16)
% 6.81/6.99          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 6.81/6.99             (k2_relat_1 @ X16))
% 6.81/6.99          | ~ (v1_relat_1 @ X17))),
% 6.81/6.99      inference('cnf', [status(esa)], [t45_relat_1])).
% 6.81/6.99  thf(d10_xboole_0, axiom,
% 6.81/6.99    (![A:$i,B:$i]:
% 6.81/6.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.81/6.99  thf('41', plain,
% 6.81/6.99      (![X0 : $i, X2 : $i]:
% 6.81/6.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.81/6.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.81/6.99  thf('42', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i]:
% 6.81/6.99         (~ (v1_relat_1 @ X1)
% 6.81/6.99          | ~ (v1_relat_1 @ X0)
% 6.81/6.99          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 6.81/6.99               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 6.81/6.99          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 6.81/6.99      inference('sup-', [status(thm)], ['40', '41'])).
% 6.81/6.99  thf('43', plain,
% 6.81/6.99      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 6.81/6.99           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 6.81/6.99        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 6.81/6.99        | ~ (v1_relat_1 @ sk_D)
% 6.81/6.99        | ~ (v1_relat_1 @ sk_C))),
% 6.81/6.99      inference('sup-', [status(thm)], ['39', '42'])).
% 6.81/6.99  thf(t71_relat_1, axiom,
% 6.81/6.99    (![A:$i]:
% 6.81/6.99     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.81/6.99       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.81/6.99  thf('44', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 6.81/6.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.81/6.99  thf('45', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 6.81/6.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.81/6.99  thf('46', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 6.81/6.99      inference('demod', [status(thm)], ['44', '45'])).
% 6.81/6.99  thf('47', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf(cc2_relset_1, axiom,
% 6.81/6.99    (![A:$i,B:$i,C:$i]:
% 6.81/6.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.81/6.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.81/6.99  thf('48', plain,
% 6.81/6.99      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.81/6.99         ((v5_relat_1 @ X22 @ X24)
% 6.81/6.99          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.81/6.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.81/6.99  thf('49', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 6.81/6.99      inference('sup-', [status(thm)], ['47', '48'])).
% 6.81/6.99  thf(d19_relat_1, axiom,
% 6.81/6.99    (![A:$i,B:$i]:
% 6.81/6.99     ( ( v1_relat_1 @ B ) =>
% 6.81/6.99       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 6.81/6.99  thf('50', plain,
% 6.81/6.99      (![X12 : $i, X13 : $i]:
% 6.81/6.99         (~ (v5_relat_1 @ X12 @ X13)
% 6.81/6.99          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 6.81/6.99          | ~ (v1_relat_1 @ X12))),
% 6.81/6.99      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.81/6.99  thf('51', plain,
% 6.81/6.99      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 6.81/6.99      inference('sup-', [status(thm)], ['49', '50'])).
% 6.81/6.99  thf('52', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf(cc2_relat_1, axiom,
% 6.81/6.99    (![A:$i]:
% 6.81/6.99     ( ( v1_relat_1 @ A ) =>
% 6.81/6.99       ( ![B:$i]:
% 6.81/6.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.81/6.99  thf('53', plain,
% 6.81/6.99      (![X10 : $i, X11 : $i]:
% 6.81/6.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 6.81/6.99          | (v1_relat_1 @ X10)
% 6.81/6.99          | ~ (v1_relat_1 @ X11))),
% 6.81/6.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.81/6.99  thf('54', plain,
% 6.81/6.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 6.81/6.99      inference('sup-', [status(thm)], ['52', '53'])).
% 6.81/6.99  thf(fc6_relat_1, axiom,
% 6.81/6.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.81/6.99  thf('55', plain,
% 6.81/6.99      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 6.81/6.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.81/6.99  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 6.81/6.99      inference('demod', [status(thm)], ['54', '55'])).
% 6.81/6.99  thf('57', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 6.81/6.99      inference('demod', [status(thm)], ['51', '56'])).
% 6.81/6.99  thf('58', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 6.81/6.99      inference('demod', [status(thm)], ['20', '21', '38'])).
% 6.81/6.99  thf('59', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 6.81/6.99      inference('demod', [status(thm)], ['44', '45'])).
% 6.81/6.99  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 6.81/6.99      inference('demod', [status(thm)], ['54', '55'])).
% 6.81/6.99  thf('61', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('62', plain,
% 6.81/6.99      (![X10 : $i, X11 : $i]:
% 6.81/6.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 6.81/6.99          | (v1_relat_1 @ X10)
% 6.81/6.99          | ~ (v1_relat_1 @ X11))),
% 6.81/6.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.81/6.99  thf('63', plain,
% 6.81/6.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 6.81/6.99      inference('sup-', [status(thm)], ['61', '62'])).
% 6.81/6.99  thf('64', plain,
% 6.81/6.99      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 6.81/6.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.81/6.99  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 6.81/6.99      inference('demod', [status(thm)], ['63', '64'])).
% 6.81/6.99  thf('66', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 6.81/6.99      inference('demod', [status(thm)],
% 6.81/6.99                ['43', '46', '57', '58', '59', '60', '65'])).
% 6.81/6.99  thf('67', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.81/6.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.81/6.99  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.81/6.99      inference('simplify', [status(thm)], ['67'])).
% 6.81/6.99  thf('69', plain,
% 6.81/6.99      (![X12 : $i, X13 : $i]:
% 6.81/6.99         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 6.81/6.99          | (v5_relat_1 @ X12 @ X13)
% 6.81/6.99          | ~ (v1_relat_1 @ X12))),
% 6.81/6.99      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.81/6.99  thf('70', plain,
% 6.81/6.99      (![X0 : $i]:
% 6.81/6.99         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 6.81/6.99      inference('sup-', [status(thm)], ['68', '69'])).
% 6.81/6.99  thf(d3_funct_2, axiom,
% 6.81/6.99    (![A:$i,B:$i]:
% 6.81/6.99     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 6.81/6.99       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 6.81/6.99  thf('71', plain,
% 6.81/6.99      (![X30 : $i, X31 : $i]:
% 6.81/6.99         (((k2_relat_1 @ X31) != (X30))
% 6.81/6.99          | (v2_funct_2 @ X31 @ X30)
% 6.81/6.99          | ~ (v5_relat_1 @ X31 @ X30)
% 6.81/6.99          | ~ (v1_relat_1 @ X31))),
% 6.81/6.99      inference('cnf', [status(esa)], [d3_funct_2])).
% 6.81/6.99  thf('72', plain,
% 6.81/6.99      (![X31 : $i]:
% 6.81/6.99         (~ (v1_relat_1 @ X31)
% 6.81/6.99          | ~ (v5_relat_1 @ X31 @ (k2_relat_1 @ X31))
% 6.81/6.99          | (v2_funct_2 @ X31 @ (k2_relat_1 @ X31)))),
% 6.81/6.99      inference('simplify', [status(thm)], ['71'])).
% 6.81/6.99  thf('73', plain,
% 6.81/6.99      (![X0 : $i]:
% 6.81/6.99         (~ (v1_relat_1 @ X0)
% 6.81/6.99          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 6.81/6.99          | ~ (v1_relat_1 @ X0))),
% 6.81/6.99      inference('sup-', [status(thm)], ['70', '72'])).
% 6.81/6.99  thf('74', plain,
% 6.81/6.99      (![X0 : $i]:
% 6.81/6.99         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 6.81/6.99      inference('simplify', [status(thm)], ['73'])).
% 6.81/6.99  thf('75', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 6.81/6.99      inference('sup+', [status(thm)], ['66', '74'])).
% 6.81/6.99  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 6.81/6.99      inference('demod', [status(thm)], ['54', '55'])).
% 6.81/6.99  thf('77', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 6.81/6.99      inference('demod', [status(thm)], ['75', '76'])).
% 6.81/6.99  thf('78', plain,
% 6.81/6.99      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 6.81/6.99      inference('split', [status(esa)], ['11'])).
% 6.81/6.99  thf('79', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 6.81/6.99      inference('sup-', [status(thm)], ['77', '78'])).
% 6.81/6.99  thf('80', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 6.81/6.99      inference('split', [status(esa)], ['11'])).
% 6.81/6.99  thf('81', plain, (~ ((v2_funct_1 @ sk_C))),
% 6.81/6.99      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 6.81/6.99  thf('82', plain, (~ (v1_xboole_0 @ sk_C)),
% 6.81/6.99      inference('simpl_trail', [status(thm)], ['13', '81'])).
% 6.81/6.99  thf('83', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf(cc1_subset_1, axiom,
% 6.81/6.99    (![A:$i]:
% 6.81/6.99     ( ( v1_xboole_0 @ A ) =>
% 6.81/6.99       ( ![B:$i]:
% 6.81/6.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 6.81/6.99  thf('84', plain,
% 6.81/6.99      (![X8 : $i, X9 : $i]:
% 6.81/6.99         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 6.81/6.99          | (v1_xboole_0 @ X8)
% 6.81/6.99          | ~ (v1_xboole_0 @ X9))),
% 6.81/6.99      inference('cnf', [status(esa)], [cc1_subset_1])).
% 6.81/6.99  thf('85', plain,
% 6.81/6.99      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 6.81/6.99      inference('sup-', [status(thm)], ['83', '84'])).
% 6.81/6.99  thf('86', plain,
% 6.81/6.99      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.81/6.99         = (k6_partfun1 @ sk_A))),
% 6.81/6.99      inference('demod', [status(thm)], ['34', '37'])).
% 6.81/6.99  thf('87', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf(t26_funct_2, axiom,
% 6.81/6.99    (![A:$i,B:$i,C:$i,D:$i]:
% 6.81/6.99     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.81/6.99         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.81/6.99       ( ![E:$i]:
% 6.81/6.99         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 6.81/6.99             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.81/6.99           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 6.81/6.99             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 6.81/6.99               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 6.81/6.99  thf('88', plain,
% 6.81/6.99      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 6.81/6.99         (~ (v1_funct_1 @ X45)
% 6.81/6.99          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 6.81/6.99          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.81/6.99          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45))
% 6.81/6.99          | (v2_funct_1 @ X49)
% 6.81/6.99          | ((X47) = (k1_xboole_0))
% 6.81/6.99          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 6.81/6.99          | ~ (v1_funct_2 @ X49 @ X48 @ X46)
% 6.81/6.99          | ~ (v1_funct_1 @ X49))),
% 6.81/6.99      inference('cnf', [status(esa)], [t26_funct_2])).
% 6.81/6.99  thf('89', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i]:
% 6.81/6.99         (~ (v1_funct_1 @ X0)
% 6.81/6.99          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.81/6.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.81/6.99          | ((sk_A) = (k1_xboole_0))
% 6.81/6.99          | (v2_funct_1 @ X0)
% 6.81/6.99          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 6.81/6.99          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 6.81/6.99          | ~ (v1_funct_1 @ sk_D))),
% 6.81/6.99      inference('sup-', [status(thm)], ['87', '88'])).
% 6.81/6.99  thf('90', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('92', plain,
% 6.81/6.99      (![X0 : $i, X1 : $i]:
% 6.81/6.99         (~ (v1_funct_1 @ X0)
% 6.81/6.99          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.81/6.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.81/6.99          | ((sk_A) = (k1_xboole_0))
% 6.81/6.99          | (v2_funct_1 @ X0)
% 6.81/6.99          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 6.81/6.99      inference('demod', [status(thm)], ['89', '90', '91'])).
% 6.81/6.99  thf('93', plain,
% 6.81/6.99      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 6.81/6.99        | (v2_funct_1 @ sk_C)
% 6.81/6.99        | ((sk_A) = (k1_xboole_0))
% 6.81/6.99        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 6.81/6.99        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 6.81/6.99        | ~ (v1_funct_1 @ sk_C))),
% 6.81/6.99      inference('sup-', [status(thm)], ['86', '92'])).
% 6.81/6.99  thf('94', plain, (![X21 : $i]: (v2_funct_1 @ (k6_partfun1 @ X21))),
% 6.81/6.99      inference('demod', [status(thm)], ['6', '7'])).
% 6.81/6.99  thf('95', plain,
% 6.81/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('96', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 6.81/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.81/6.99  thf('98', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 6.81/6.99      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 6.81/6.99  thf('99', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.81/6.99      inference('split', [status(esa)], ['11'])).
% 6.81/6.99  thf('100', plain, (~ ((v2_funct_1 @ sk_C))),
% 6.81/6.99      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 6.81/6.99  thf('101', plain, (~ (v2_funct_1 @ sk_C)),
% 6.81/6.99      inference('simpl_trail', [status(thm)], ['99', '100'])).
% 6.81/6.99  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 6.81/6.99      inference('clc', [status(thm)], ['98', '101'])).
% 6.81/6.99  thf(t113_zfmisc_1, axiom,
% 6.81/6.99    (![A:$i,B:$i]:
% 6.81/6.99     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.81/6.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.81/6.99  thf('103', plain,
% 6.81/6.99      (![X6 : $i, X7 : $i]:
% 6.81/6.99         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 6.81/6.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.81/6.99  thf('104', plain,
% 6.81/6.99      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 6.81/6.99      inference('simplify', [status(thm)], ['103'])).
% 6.81/6.99  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.81/6.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.81/6.99  thf('106', plain, ((v1_xboole_0 @ sk_C)),
% 6.81/6.99      inference('demod', [status(thm)], ['85', '102', '104', '105'])).
% 6.81/6.99  thf('107', plain, ($false), inference('demod', [status(thm)], ['82', '106'])).
% 6.81/6.99  
% 6.81/6.99  % SZS output end Refutation
% 6.81/6.99  
% 6.81/7.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
