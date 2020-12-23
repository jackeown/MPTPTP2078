%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p2gEmbwe2W

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:24 EST 2020

% Result     : Theorem 3.96s
% Output     : Refutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 313 expanded)
%              Number of leaves         :   39 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          : 1053 (6317 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('7',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
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

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['31','34','35','40'])).

thf('42',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('45',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['13','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('63',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('64',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
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

thf('68',plain,(
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

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('80',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['78','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['49','82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['46','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p2gEmbwe2W
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.96/4.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.96/4.14  % Solved by: fo/fo7.sh
% 3.96/4.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.96/4.14  % done 3345 iterations in 3.682s
% 3.96/4.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.96/4.14  % SZS output start Refutation
% 3.96/4.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.96/4.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.96/4.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.96/4.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.96/4.14  thf(sk_D_type, type, sk_D: $i).
% 3.96/4.14  thf(sk_C_type, type, sk_C: $i).
% 3.96/4.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.96/4.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.96/4.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.96/4.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.96/4.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.96/4.14  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.96/4.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.96/4.14  thf(sk_A_type, type, sk_A: $i).
% 3.96/4.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.96/4.14  thf(sk_B_type, type, sk_B: $i).
% 3.96/4.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.96/4.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.96/4.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.96/4.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.96/4.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.96/4.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.96/4.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.96/4.14  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.96/4.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.96/4.14  thf(t8_boole, axiom,
% 3.96/4.14    (![A:$i,B:$i]:
% 3.96/4.14     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.96/4.14  thf('1', plain,
% 3.96/4.14      (![X0 : $i, X1 : $i]:
% 3.96/4.14         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.96/4.14      inference('cnf', [status(esa)], [t8_boole])).
% 3.96/4.14  thf('2', plain,
% 3.96/4.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.96/4.14      inference('sup-', [status(thm)], ['0', '1'])).
% 3.96/4.14  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.96/4.14  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.96/4.14      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.96/4.14  thf(redefinition_k6_partfun1, axiom,
% 3.96/4.14    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.96/4.14  thf('4', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.96/4.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.96/4.14  thf('5', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.96/4.14      inference('demod', [status(thm)], ['3', '4'])).
% 3.96/4.14  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.96/4.14  thf('6', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 3.96/4.14      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.96/4.14  thf('7', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.96/4.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.96/4.14  thf('8', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 3.96/4.14      inference('demod', [status(thm)], ['6', '7'])).
% 3.96/4.14  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.96/4.14      inference('sup+', [status(thm)], ['5', '8'])).
% 3.96/4.14  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.96/4.14      inference('sup+', [status(thm)], ['2', '9'])).
% 3.96/4.14  thf(t29_funct_2, conjecture,
% 3.96/4.14    (![A:$i,B:$i,C:$i]:
% 3.96/4.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.96/4.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.96/4.14       ( ![D:$i]:
% 3.96/4.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.96/4.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.96/4.14           ( ( r2_relset_1 @
% 3.96/4.14               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.96/4.14               ( k6_partfun1 @ A ) ) =>
% 3.96/4.14             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.96/4.14  thf(zf_stmt_0, negated_conjecture,
% 3.96/4.14    (~( ![A:$i,B:$i,C:$i]:
% 3.96/4.14        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.96/4.14            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.96/4.14          ( ![D:$i]:
% 3.96/4.14            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.96/4.14                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.96/4.14              ( ( r2_relset_1 @
% 3.96/4.14                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.96/4.14                  ( k6_partfun1 @ A ) ) =>
% 3.96/4.14                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.96/4.14    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.96/4.14  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.96/4.14      inference('split', [status(esa)], ['11'])).
% 3.96/4.14  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.96/4.14      inference('sup-', [status(thm)], ['10', '12'])).
% 3.96/4.14  thf('14', plain,
% 3.96/4.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.96/4.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.96/4.14        (k6_partfun1 @ sk_A))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('15', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf(t24_funct_2, axiom,
% 3.96/4.14    (![A:$i,B:$i,C:$i]:
% 3.96/4.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.96/4.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.96/4.14       ( ![D:$i]:
% 3.96/4.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.96/4.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.96/4.14           ( ( r2_relset_1 @
% 3.96/4.14               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.96/4.14               ( k6_partfun1 @ B ) ) =>
% 3.96/4.14             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.96/4.14  thf('16', plain,
% 3.96/4.14      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.96/4.14         (~ (v1_funct_1 @ X30)
% 3.96/4.14          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 3.96/4.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.96/4.14          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 3.96/4.14               (k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33) @ 
% 3.96/4.14               (k6_partfun1 @ X31))
% 3.96/4.14          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 3.96/4.14          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 3.96/4.14          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 3.96/4.14          | ~ (v1_funct_1 @ X33))),
% 3.96/4.14      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.96/4.14  thf('17', plain,
% 3.96/4.14      (![X0 : $i]:
% 3.96/4.14         (~ (v1_funct_1 @ X0)
% 3.96/4.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.96/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.96/4.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.96/4.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.96/4.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.96/4.14               (k6_partfun1 @ sk_A))
% 3.96/4.14          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.96/4.14          | ~ (v1_funct_1 @ sk_C))),
% 3.96/4.14      inference('sup-', [status(thm)], ['15', '16'])).
% 3.96/4.14  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('20', plain,
% 3.96/4.14      (![X0 : $i]:
% 3.96/4.14         (~ (v1_funct_1 @ X0)
% 3.96/4.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.96/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.96/4.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.96/4.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.96/4.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.96/4.14               (k6_partfun1 @ sk_A)))),
% 3.96/4.14      inference('demod', [status(thm)], ['17', '18', '19'])).
% 3.96/4.14  thf('21', plain,
% 3.96/4.14      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.96/4.14        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.96/4.14        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.96/4.14        | ~ (v1_funct_1 @ sk_D))),
% 3.96/4.14      inference('sup-', [status(thm)], ['14', '20'])).
% 3.96/4.14  thf('22', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf(redefinition_k2_relset_1, axiom,
% 3.96/4.14    (![A:$i,B:$i,C:$i]:
% 3.96/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.96/4.14       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.96/4.14  thf('23', plain,
% 3.96/4.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.96/4.14         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 3.96/4.14          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.96/4.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.96/4.14  thf('24', plain,
% 3.96/4.14      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.96/4.14      inference('sup-', [status(thm)], ['22', '23'])).
% 3.96/4.14  thf('25', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.96/4.14      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.96/4.14  thf(d3_funct_2, axiom,
% 3.96/4.14    (![A:$i,B:$i]:
% 3.96/4.14     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.96/4.14       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.96/4.14  thf('29', plain,
% 3.96/4.14      (![X21 : $i, X22 : $i]:
% 3.96/4.14         (((k2_relat_1 @ X22) != (X21))
% 3.96/4.14          | (v2_funct_2 @ X22 @ X21)
% 3.96/4.14          | ~ (v5_relat_1 @ X22 @ X21)
% 3.96/4.14          | ~ (v1_relat_1 @ X22))),
% 3.96/4.14      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.96/4.14  thf('30', plain,
% 3.96/4.14      (![X22 : $i]:
% 3.96/4.14         (~ (v1_relat_1 @ X22)
% 3.96/4.14          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 3.96/4.14          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 3.96/4.14      inference('simplify', [status(thm)], ['29'])).
% 3.96/4.14  thf('31', plain,
% 3.96/4.14      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.96/4.14        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.96/4.14        | ~ (v1_relat_1 @ sk_D))),
% 3.96/4.14      inference('sup-', [status(thm)], ['28', '30'])).
% 3.96/4.14  thf('32', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf(cc2_relset_1, axiom,
% 3.96/4.14    (![A:$i,B:$i,C:$i]:
% 3.96/4.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.96/4.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.96/4.14  thf('33', plain,
% 3.96/4.14      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.96/4.14         ((v5_relat_1 @ X7 @ X9)
% 3.96/4.14          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.96/4.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.96/4.14  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.96/4.14      inference('sup-', [status(thm)], ['32', '33'])).
% 3.96/4.14  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.96/4.14      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.96/4.14  thf('36', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf(cc2_relat_1, axiom,
% 3.96/4.14    (![A:$i]:
% 3.96/4.14     ( ( v1_relat_1 @ A ) =>
% 3.96/4.14       ( ![B:$i]:
% 3.96/4.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.96/4.14  thf('37', plain,
% 3.96/4.14      (![X2 : $i, X3 : $i]:
% 3.96/4.14         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 3.96/4.14          | (v1_relat_1 @ X2)
% 3.96/4.14          | ~ (v1_relat_1 @ X3))),
% 3.96/4.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.96/4.14  thf('38', plain,
% 3.96/4.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.96/4.14      inference('sup-', [status(thm)], ['36', '37'])).
% 3.96/4.14  thf(fc6_relat_1, axiom,
% 3.96/4.14    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.96/4.14  thf('39', plain,
% 3.96/4.14      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 3.96/4.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.96/4.14  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 3.96/4.14      inference('demod', [status(thm)], ['38', '39'])).
% 3.96/4.14  thf('41', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.96/4.14      inference('demod', [status(thm)], ['31', '34', '35', '40'])).
% 3.96/4.14  thf('42', plain,
% 3.96/4.14      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.96/4.14      inference('split', [status(esa)], ['11'])).
% 3.96/4.14  thf('43', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.96/4.14      inference('sup-', [status(thm)], ['41', '42'])).
% 3.96/4.14  thf('44', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.96/4.14      inference('split', [status(esa)], ['11'])).
% 3.96/4.14  thf('45', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.96/4.14      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 3.96/4.14  thf('46', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.96/4.14      inference('simpl_trail', [status(thm)], ['13', '45'])).
% 3.96/4.14  thf('47', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf(cc3_relset_1, axiom,
% 3.96/4.14    (![A:$i,B:$i]:
% 3.96/4.14     ( ( v1_xboole_0 @ A ) =>
% 3.96/4.14       ( ![C:$i]:
% 3.96/4.14         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.96/4.14           ( v1_xboole_0 @ C ) ) ) ))).
% 3.96/4.14  thf('48', plain,
% 3.96/4.14      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.96/4.14         (~ (v1_xboole_0 @ X10)
% 3.96/4.14          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 3.96/4.14          | (v1_xboole_0 @ X11))),
% 3.96/4.14      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.96/4.14  thf('49', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.96/4.14      inference('sup-', [status(thm)], ['47', '48'])).
% 3.96/4.14  thf('50', plain,
% 3.96/4.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.96/4.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.96/4.14        (k6_partfun1 @ sk_A))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('51', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('52', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf(dt_k1_partfun1, axiom,
% 3.96/4.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.96/4.14     ( ( ( v1_funct_1 @ E ) & 
% 3.96/4.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.96/4.14         ( v1_funct_1 @ F ) & 
% 3.96/4.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.96/4.14       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.96/4.14         ( m1_subset_1 @
% 3.96/4.14           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.96/4.14           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.96/4.14  thf('53', plain,
% 3.96/4.14      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.96/4.14         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 3.96/4.14          | ~ (v1_funct_1 @ X23)
% 3.96/4.14          | ~ (v1_funct_1 @ X26)
% 3.96/4.14          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.96/4.14          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 3.96/4.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 3.96/4.14      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.96/4.14  thf('54', plain,
% 3.96/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.96/4.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.96/4.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.96/4.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.96/4.14          | ~ (v1_funct_1 @ X1)
% 3.96/4.14          | ~ (v1_funct_1 @ sk_C))),
% 3.96/4.14      inference('sup-', [status(thm)], ['52', '53'])).
% 3.96/4.14  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('56', plain,
% 3.96/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.96/4.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.96/4.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.96/4.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.96/4.14          | ~ (v1_funct_1 @ X1))),
% 3.96/4.14      inference('demod', [status(thm)], ['54', '55'])).
% 3.96/4.14  thf('57', plain,
% 3.96/4.14      ((~ (v1_funct_1 @ sk_D)
% 3.96/4.14        | (m1_subset_1 @ 
% 3.96/4.14           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.96/4.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.96/4.14      inference('sup-', [status(thm)], ['51', '56'])).
% 3.96/4.14  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('59', plain,
% 3.96/4.14      ((m1_subset_1 @ 
% 3.96/4.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.96/4.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.96/4.14      inference('demod', [status(thm)], ['57', '58'])).
% 3.96/4.14  thf(redefinition_r2_relset_1, axiom,
% 3.96/4.14    (![A:$i,B:$i,C:$i,D:$i]:
% 3.96/4.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.96/4.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.96/4.14       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.96/4.14  thf('60', plain,
% 3.96/4.14      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.96/4.14         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 3.96/4.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 3.96/4.14          | ((X16) = (X19))
% 3.96/4.14          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 3.96/4.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.96/4.14  thf('61', plain,
% 3.96/4.14      (![X0 : $i]:
% 3.96/4.14         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.96/4.14             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.96/4.14          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.96/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.96/4.14      inference('sup-', [status(thm)], ['59', '60'])).
% 3.96/4.14  thf('62', plain,
% 3.96/4.14      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.96/4.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.96/4.14        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.96/4.14            = (k6_partfun1 @ sk_A)))),
% 3.96/4.14      inference('sup-', [status(thm)], ['50', '61'])).
% 3.96/4.14  thf(t29_relset_1, axiom,
% 3.96/4.14    (![A:$i]:
% 3.96/4.14     ( m1_subset_1 @
% 3.96/4.14       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.96/4.14  thf('63', plain,
% 3.96/4.14      (![X20 : $i]:
% 3.96/4.14         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 3.96/4.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 3.96/4.14      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.96/4.14  thf('64', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.96/4.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.96/4.14  thf('65', plain,
% 3.96/4.14      (![X20 : $i]:
% 3.96/4.14         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 3.96/4.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 3.96/4.14      inference('demod', [status(thm)], ['63', '64'])).
% 3.96/4.14  thf('66', plain,
% 3.96/4.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.96/4.14         = (k6_partfun1 @ sk_A))),
% 3.96/4.14      inference('demod', [status(thm)], ['62', '65'])).
% 3.96/4.14  thf('67', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf(t26_funct_2, axiom,
% 3.96/4.14    (![A:$i,B:$i,C:$i,D:$i]:
% 3.96/4.14     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.96/4.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.96/4.14       ( ![E:$i]:
% 3.96/4.14         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.96/4.14             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.96/4.14           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.96/4.14             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.96/4.14               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.96/4.14  thf('68', plain,
% 3.96/4.14      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.96/4.14         (~ (v1_funct_1 @ X34)
% 3.96/4.14          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 3.96/4.14          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.96/4.14          | ~ (v2_funct_1 @ (k1_partfun1 @ X37 @ X35 @ X35 @ X36 @ X38 @ X34))
% 3.96/4.14          | (v2_funct_1 @ X38)
% 3.96/4.14          | ((X36) = (k1_xboole_0))
% 3.96/4.14          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 3.96/4.14          | ~ (v1_funct_2 @ X38 @ X37 @ X35)
% 3.96/4.14          | ~ (v1_funct_1 @ X38))),
% 3.96/4.14      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.96/4.14  thf('69', plain,
% 3.96/4.14      (![X0 : $i, X1 : $i]:
% 3.96/4.14         (~ (v1_funct_1 @ X0)
% 3.96/4.14          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.96/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.96/4.14          | ((sk_A) = (k1_xboole_0))
% 3.96/4.14          | (v2_funct_1 @ X0)
% 3.96/4.14          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.96/4.14          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.96/4.14          | ~ (v1_funct_1 @ sk_D))),
% 3.96/4.14      inference('sup-', [status(thm)], ['67', '68'])).
% 3.96/4.14  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('72', plain,
% 3.96/4.14      (![X0 : $i, X1 : $i]:
% 3.96/4.14         (~ (v1_funct_1 @ X0)
% 3.96/4.14          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.96/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.96/4.14          | ((sk_A) = (k1_xboole_0))
% 3.96/4.14          | (v2_funct_1 @ X0)
% 3.96/4.14          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.96/4.14      inference('demod', [status(thm)], ['69', '70', '71'])).
% 3.96/4.14  thf('73', plain,
% 3.96/4.14      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.96/4.14        | (v2_funct_1 @ sk_C)
% 3.96/4.14        | ((sk_A) = (k1_xboole_0))
% 3.96/4.14        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.96/4.14        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.96/4.14        | ~ (v1_funct_1 @ sk_C))),
% 3.96/4.14      inference('sup-', [status(thm)], ['66', '72'])).
% 3.96/4.14  thf('74', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 3.96/4.14      inference('demod', [status(thm)], ['6', '7'])).
% 3.96/4.14  thf('75', plain,
% 3.96/4.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 3.96/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.14  thf('78', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.96/4.14      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 3.96/4.14  thf('79', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.96/4.14      inference('split', [status(esa)], ['11'])).
% 3.96/4.14  thf('80', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.96/4.14      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 3.96/4.14  thf('81', plain, (~ (v2_funct_1 @ sk_C)),
% 3.96/4.14      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 3.96/4.14  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 3.96/4.14      inference('clc', [status(thm)], ['78', '81'])).
% 3.96/4.14  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.96/4.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.96/4.14  thf('84', plain, ((v1_xboole_0 @ sk_C)),
% 3.96/4.14      inference('demod', [status(thm)], ['49', '82', '83'])).
% 3.96/4.14  thf('85', plain, ($false), inference('demod', [status(thm)], ['46', '84'])).
% 3.96/4.14  
% 3.96/4.14  % SZS output end Refutation
% 3.96/4.14  
% 3.96/4.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
