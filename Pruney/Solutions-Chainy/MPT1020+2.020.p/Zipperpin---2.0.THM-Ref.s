%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3N5hxXKXR9

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:03 EST 2020

% Result     : Theorem 11.52s
% Output     : Refutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 255 expanded)
%              Number of leaves         :   39 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          : 1384 (5761 expanded)
%              Number of equality atoms :   53 (  66 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_funct_2 @ X34 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('17',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('23',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ ( k6_partfun1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( X39
        = ( k2_funct_1 @ X42 ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X40 @ X40 @ X41 @ X42 @ X39 ) @ ( k6_partfun1 @ X41 ) )
      | ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
       != X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_2 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('71',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('75',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_2 @ X22 @ X21 )
      | ( ( k2_relat_1 @ X22 )
        = X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('78',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('81',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['76','79','82'])).

thf('84',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['68','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('87',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','84','90'])).

thf('92',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('95',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','99'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['38','100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3N5hxXKXR9
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 11.52/11.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.52/11.69  % Solved by: fo/fo7.sh
% 11.52/11.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.52/11.69  % done 7467 iterations in 11.234s
% 11.52/11.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.52/11.69  % SZS output start Refutation
% 11.52/11.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.52/11.69  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 11.52/11.69  thf(sk_C_type, type, sk_C: $i).
% 11.52/11.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.52/11.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.52/11.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.52/11.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 11.52/11.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.52/11.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 11.52/11.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.52/11.69  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 11.52/11.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.52/11.69  thf(sk_A_type, type, sk_A: $i).
% 11.52/11.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 11.52/11.69  thf(sk_B_type, type, sk_B: $i).
% 11.52/11.69  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 11.52/11.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 11.52/11.69  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 11.52/11.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 11.52/11.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.52/11.69  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 11.52/11.69  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 11.52/11.69  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 11.52/11.69  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 11.52/11.69  thf(t87_funct_2, conjecture,
% 11.52/11.69    (![A:$i,B:$i]:
% 11.52/11.69     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.52/11.69         ( v3_funct_2 @ B @ A @ A ) & 
% 11.52/11.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.52/11.69       ( ![C:$i]:
% 11.52/11.69         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 11.52/11.69             ( v3_funct_2 @ C @ A @ A ) & 
% 11.52/11.69             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.52/11.69           ( ( r2_relset_1 @
% 11.52/11.69               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 11.52/11.69               ( k6_partfun1 @ A ) ) =>
% 11.52/11.69             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 11.52/11.69  thf(zf_stmt_0, negated_conjecture,
% 11.52/11.69    (~( ![A:$i,B:$i]:
% 11.52/11.69        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.52/11.69            ( v3_funct_2 @ B @ A @ A ) & 
% 11.52/11.69            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.52/11.69          ( ![C:$i]:
% 11.52/11.69            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 11.52/11.69                ( v3_funct_2 @ C @ A @ A ) & 
% 11.52/11.69                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.52/11.69              ( ( r2_relset_1 @
% 11.52/11.69                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 11.52/11.69                  ( k6_partfun1 @ A ) ) =>
% 11.52/11.69                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 11.52/11.69    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 11.52/11.69  thf('0', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(dt_k2_funct_2, axiom,
% 11.52/11.69    (![A:$i,B:$i]:
% 11.52/11.69     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.52/11.69         ( v3_funct_2 @ B @ A @ A ) & 
% 11.52/11.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.52/11.69       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 11.52/11.69         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 11.52/11.69         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 11.52/11.69         ( m1_subset_1 @
% 11.52/11.69           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 11.52/11.69  thf('1', plain,
% 11.52/11.69      (![X29 : $i, X30 : $i]:
% 11.52/11.69         ((m1_subset_1 @ (k2_funct_2 @ X29 @ X30) @ 
% 11.52/11.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 11.52/11.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 11.52/11.69          | ~ (v3_funct_2 @ X30 @ X29 @ X29)
% 11.52/11.69          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 11.52/11.69          | ~ (v1_funct_1 @ X30))),
% 11.52/11.69      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 11.52/11.69  thf('2', plain,
% 11.52/11.69      ((~ (v1_funct_1 @ sk_B)
% 11.52/11.69        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.52/11.69        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.52/11.69        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 11.52/11.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.52/11.69      inference('sup-', [status(thm)], ['0', '1'])).
% 11.52/11.69  thf('3', plain, ((v1_funct_1 @ sk_B)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('4', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('5', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('6', plain,
% 11.52/11.69      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 11.52/11.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 11.52/11.69  thf('7', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(redefinition_k2_funct_2, axiom,
% 11.52/11.69    (![A:$i,B:$i]:
% 11.52/11.69     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.52/11.69         ( v3_funct_2 @ B @ A @ A ) & 
% 11.52/11.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.52/11.69       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 11.52/11.69  thf('8', plain,
% 11.52/11.69      (![X33 : $i, X34 : $i]:
% 11.52/11.69         (((k2_funct_2 @ X34 @ X33) = (k2_funct_1 @ X33))
% 11.52/11.69          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 11.52/11.69          | ~ (v3_funct_2 @ X33 @ X34 @ X34)
% 11.52/11.69          | ~ (v1_funct_2 @ X33 @ X34 @ X34)
% 11.52/11.69          | ~ (v1_funct_1 @ X33))),
% 11.52/11.69      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 11.52/11.69  thf('9', plain,
% 11.52/11.69      ((~ (v1_funct_1 @ sk_B)
% 11.52/11.69        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.52/11.69        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.52/11.69        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 11.52/11.69      inference('sup-', [status(thm)], ['7', '8'])).
% 11.52/11.69  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('11', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('12', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('13', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 11.52/11.69      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 11.52/11.69  thf('14', plain,
% 11.52/11.69      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 11.52/11.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('demod', [status(thm)], ['6', '13'])).
% 11.52/11.69  thf(cc4_relset_1, axiom,
% 11.52/11.69    (![A:$i,B:$i]:
% 11.52/11.69     ( ( v1_xboole_0 @ A ) =>
% 11.52/11.69       ( ![C:$i]:
% 11.52/11.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 11.52/11.69           ( v1_xboole_0 @ C ) ) ) ))).
% 11.52/11.69  thf('15', plain,
% 11.52/11.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 11.52/11.69         (~ (v1_xboole_0 @ X8)
% 11.52/11.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 11.52/11.69          | (v1_xboole_0 @ X9))),
% 11.52/11.69      inference('cnf', [status(esa)], [cc4_relset_1])).
% 11.52/11.69  thf('16', plain,
% 11.52/11.69      (((v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 11.52/11.69      inference('sup-', [status(thm)], ['14', '15'])).
% 11.52/11.69  thf(dt_k6_partfun1, axiom,
% 11.52/11.69    (![A:$i]:
% 11.52/11.69     ( ( m1_subset_1 @
% 11.52/11.69         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 11.52/11.69       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 11.52/11.69  thf('17', plain,
% 11.52/11.69      (![X32 : $i]:
% 11.52/11.69         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 11.52/11.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 11.52/11.69      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 11.52/11.69  thf('18', plain,
% 11.52/11.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 11.52/11.69         (~ (v1_xboole_0 @ X8)
% 11.52/11.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 11.52/11.69          | (v1_xboole_0 @ X9))),
% 11.52/11.69      inference('cnf', [status(esa)], [cc4_relset_1])).
% 11.52/11.69  thf('19', plain,
% 11.52/11.69      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 11.52/11.69      inference('sup-', [status(thm)], ['17', '18'])).
% 11.52/11.69  thf(t8_boole, axiom,
% 11.52/11.69    (![A:$i,B:$i]:
% 11.52/11.69     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 11.52/11.69  thf('20', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i]:
% 11.52/11.69         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 11.52/11.69      inference('cnf', [status(esa)], [t8_boole])).
% 11.52/11.69  thf('21', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i]:
% 11.52/11.69         (~ (v1_xboole_0 @ X0)
% 11.52/11.69          | ((k6_partfun1 @ X0) = (X1))
% 11.52/11.69          | ~ (v1_xboole_0 @ X1))),
% 11.52/11.69      inference('sup-', [status(thm)], ['19', '20'])).
% 11.52/11.69  thf('22', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i]:
% 11.52/11.69         (~ (v1_xboole_0 @ X0)
% 11.52/11.69          | ((k6_partfun1 @ X0) = (X1))
% 11.52/11.69          | ~ (v1_xboole_0 @ X1))),
% 11.52/11.69      inference('sup-', [status(thm)], ['19', '20'])).
% 11.52/11.69  thf('23', plain,
% 11.52/11.69      (![X32 : $i]:
% 11.52/11.69         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 11.52/11.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 11.52/11.69      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 11.52/11.69  thf(redefinition_r2_relset_1, axiom,
% 11.52/11.69    (![A:$i,B:$i,C:$i,D:$i]:
% 11.52/11.69     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.52/11.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.52/11.69       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 11.52/11.69  thf('24', plain,
% 11.52/11.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 11.52/11.69         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 11.52/11.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 11.52/11.69          | (r2_relset_1 @ X15 @ X16 @ X14 @ X17)
% 11.52/11.69          | ((X14) != (X17)))),
% 11.52/11.69      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.52/11.69  thf('25', plain,
% 11.52/11.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 11.52/11.69         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 11.52/11.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 11.52/11.69      inference('simplify', [status(thm)], ['24'])).
% 11.52/11.69  thf('26', plain,
% 11.52/11.69      (![X0 : $i]:
% 11.52/11.69         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 11.52/11.69      inference('sup-', [status(thm)], ['23', '25'])).
% 11.52/11.69  thf('27', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i]:
% 11.52/11.69         ((r2_relset_1 @ X1 @ X1 @ X0 @ (k6_partfun1 @ X1))
% 11.52/11.69          | ~ (v1_xboole_0 @ X0)
% 11.52/11.69          | ~ (v1_xboole_0 @ X1))),
% 11.52/11.69      inference('sup+', [status(thm)], ['22', '26'])).
% 11.52/11.69  thf('28', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.52/11.69         ((r2_relset_1 @ X1 @ X1 @ X2 @ X0)
% 11.52/11.69          | ~ (v1_xboole_0 @ X0)
% 11.52/11.69          | ~ (v1_xboole_0 @ X1)
% 11.52/11.69          | ~ (v1_xboole_0 @ X1)
% 11.52/11.69          | ~ (v1_xboole_0 @ X2))),
% 11.52/11.69      inference('sup+', [status(thm)], ['21', '27'])).
% 11.52/11.69  thf('29', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.52/11.69         (~ (v1_xboole_0 @ X2)
% 11.52/11.69          | ~ (v1_xboole_0 @ X1)
% 11.52/11.69          | ~ (v1_xboole_0 @ X0)
% 11.52/11.69          | (r2_relset_1 @ X1 @ X1 @ X2 @ X0))),
% 11.52/11.69      inference('simplify', [status(thm)], ['28'])).
% 11.52/11.69  thf('30', plain,
% 11.52/11.69      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('31', plain,
% 11.52/11.69      ((~ (v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B))
% 11.52/11.69        | ~ (v1_xboole_0 @ sk_A)
% 11.52/11.69        | ~ (v1_xboole_0 @ sk_C))),
% 11.52/11.69      inference('sup-', [status(thm)], ['29', '30'])).
% 11.52/11.69  thf('32', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('33', plain,
% 11.52/11.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 11.52/11.69         (~ (v1_xboole_0 @ X8)
% 11.52/11.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 11.52/11.69          | (v1_xboole_0 @ X9))),
% 11.52/11.69      inference('cnf', [status(esa)], [cc4_relset_1])).
% 11.52/11.69  thf('34', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 11.52/11.69      inference('sup-', [status(thm)], ['32', '33'])).
% 11.52/11.69  thf('35', plain,
% 11.52/11.69      ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 11.52/11.69      inference('clc', [status(thm)], ['31', '34'])).
% 11.52/11.69  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 11.52/11.69      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 11.52/11.69  thf('37', plain,
% 11.52/11.69      ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 11.52/11.69      inference('demod', [status(thm)], ['35', '36'])).
% 11.52/11.69  thf('38', plain, (~ (v1_xboole_0 @ sk_A)),
% 11.52/11.69      inference('clc', [status(thm)], ['16', '37'])).
% 11.52/11.69  thf('39', plain,
% 11.52/11.69      ((r2_relset_1 @ sk_A @ sk_A @ 
% 11.52/11.69        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 11.52/11.69        (k6_partfun1 @ sk_A))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('40', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('41', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(dt_k1_partfun1, axiom,
% 11.52/11.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.52/11.69     ( ( ( v1_funct_1 @ E ) & 
% 11.52/11.69         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.52/11.69         ( v1_funct_1 @ F ) & 
% 11.52/11.69         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 11.52/11.69       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 11.52/11.69         ( m1_subset_1 @
% 11.52/11.69           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 11.52/11.69           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 11.52/11.69  thf('42', plain,
% 11.52/11.69      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 11.52/11.69         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 11.52/11.69          | ~ (v1_funct_1 @ X23)
% 11.52/11.69          | ~ (v1_funct_1 @ X26)
% 11.52/11.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 11.52/11.69          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 11.52/11.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 11.52/11.69      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 11.52/11.69  thf('43', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.52/11.69         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 11.52/11.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 11.52/11.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 11.52/11.69          | ~ (v1_funct_1 @ X1)
% 11.52/11.69          | ~ (v1_funct_1 @ sk_B))),
% 11.52/11.69      inference('sup-', [status(thm)], ['41', '42'])).
% 11.52/11.69  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('45', plain,
% 11.52/11.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.52/11.69         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 11.52/11.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 11.52/11.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 11.52/11.69          | ~ (v1_funct_1 @ X1))),
% 11.52/11.69      inference('demod', [status(thm)], ['43', '44'])).
% 11.52/11.69  thf('46', plain,
% 11.52/11.69      ((~ (v1_funct_1 @ sk_C)
% 11.52/11.69        | (m1_subset_1 @ 
% 11.52/11.69           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 11.52/11.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.52/11.69      inference('sup-', [status(thm)], ['40', '45'])).
% 11.52/11.69  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('48', plain,
% 11.52/11.69      ((m1_subset_1 @ 
% 11.52/11.69        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 11.52/11.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('demod', [status(thm)], ['46', '47'])).
% 11.52/11.69  thf('49', plain,
% 11.52/11.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 11.52/11.69         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 11.52/11.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 11.52/11.69          | ((X14) = (X17))
% 11.52/11.69          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 11.52/11.69      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.52/11.69  thf('50', plain,
% 11.52/11.69      (![X0 : $i]:
% 11.52/11.69         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.52/11.69             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 11.52/11.69          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 11.52/11.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.52/11.69      inference('sup-', [status(thm)], ['48', '49'])).
% 11.52/11.69  thf('51', plain,
% 11.52/11.69      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 11.52/11.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.52/11.69        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 11.52/11.69            = (k6_partfun1 @ sk_A)))),
% 11.52/11.69      inference('sup-', [status(thm)], ['39', '50'])).
% 11.52/11.69  thf('52', plain,
% 11.52/11.69      (![X32 : $i]:
% 11.52/11.69         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 11.52/11.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 11.52/11.69      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 11.52/11.69  thf('53', plain,
% 11.52/11.69      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 11.52/11.69         = (k6_partfun1 @ sk_A))),
% 11.52/11.69      inference('demod', [status(thm)], ['51', '52'])).
% 11.52/11.69  thf('54', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(t36_funct_2, axiom,
% 11.52/11.69    (![A:$i,B:$i,C:$i]:
% 11.52/11.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.52/11.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.52/11.69       ( ![D:$i]:
% 11.52/11.69         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 11.52/11.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 11.52/11.69           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 11.52/11.69               ( r2_relset_1 @
% 11.52/11.69                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 11.52/11.69                 ( k6_partfun1 @ A ) ) & 
% 11.52/11.69               ( v2_funct_1 @ C ) ) =>
% 11.52/11.69             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 11.52/11.69               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 11.52/11.69  thf('55', plain,
% 11.52/11.69      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 11.52/11.69         (~ (v1_funct_1 @ X39)
% 11.52/11.69          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 11.52/11.69          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 11.52/11.69          | ((X39) = (k2_funct_1 @ X42))
% 11.52/11.69          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 11.52/11.69               (k1_partfun1 @ X41 @ X40 @ X40 @ X41 @ X42 @ X39) @ 
% 11.52/11.69               (k6_partfun1 @ X41))
% 11.52/11.69          | ((X40) = (k1_xboole_0))
% 11.52/11.69          | ((X41) = (k1_xboole_0))
% 11.52/11.69          | ~ (v2_funct_1 @ X42)
% 11.52/11.69          | ((k2_relset_1 @ X41 @ X40 @ X42) != (X40))
% 11.52/11.69          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 11.52/11.69          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 11.52/11.69          | ~ (v1_funct_1 @ X42))),
% 11.52/11.69      inference('cnf', [status(esa)], [t36_funct_2])).
% 11.52/11.69  thf('56', plain,
% 11.52/11.69      (![X0 : $i]:
% 11.52/11.69         (~ (v1_funct_1 @ X0)
% 11.52/11.69          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.52/11.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.52/11.69          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 11.52/11.69          | ~ (v2_funct_1 @ X0)
% 11.52/11.69          | ((sk_A) = (k1_xboole_0))
% 11.52/11.69          | ((sk_A) = (k1_xboole_0))
% 11.52/11.69          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.52/11.69               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 11.52/11.69               (k6_partfun1 @ sk_A))
% 11.52/11.69          | ((sk_C) = (k2_funct_1 @ X0))
% 11.52/11.69          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 11.52/11.69          | ~ (v1_funct_1 @ sk_C))),
% 11.52/11.69      inference('sup-', [status(thm)], ['54', '55'])).
% 11.52/11.69  thf('57', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('59', plain,
% 11.52/11.69      (![X0 : $i]:
% 11.52/11.69         (~ (v1_funct_1 @ X0)
% 11.52/11.69          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.52/11.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.52/11.69          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 11.52/11.69          | ~ (v2_funct_1 @ X0)
% 11.52/11.69          | ((sk_A) = (k1_xboole_0))
% 11.52/11.69          | ((sk_A) = (k1_xboole_0))
% 11.52/11.69          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.52/11.69               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 11.52/11.69               (k6_partfun1 @ sk_A))
% 11.52/11.69          | ((sk_C) = (k2_funct_1 @ X0)))),
% 11.52/11.69      inference('demod', [status(thm)], ['56', '57', '58'])).
% 11.52/11.69  thf('60', plain,
% 11.52/11.69      (![X0 : $i]:
% 11.52/11.69         (((sk_C) = (k2_funct_1 @ X0))
% 11.52/11.69          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.52/11.69               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 11.52/11.69               (k6_partfun1 @ sk_A))
% 11.52/11.69          | ((sk_A) = (k1_xboole_0))
% 11.52/11.69          | ~ (v2_funct_1 @ X0)
% 11.52/11.69          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 11.52/11.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.52/11.69          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.52/11.69          | ~ (v1_funct_1 @ X0))),
% 11.52/11.69      inference('simplify', [status(thm)], ['59'])).
% 11.52/11.69  thf('61', plain,
% 11.52/11.69      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 11.52/11.69           (k6_partfun1 @ sk_A))
% 11.52/11.69        | ~ (v1_funct_1 @ sk_B)
% 11.52/11.69        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.52/11.69        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.52/11.69        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 11.52/11.69        | ~ (v2_funct_1 @ sk_B)
% 11.52/11.69        | ((sk_A) = (k1_xboole_0))
% 11.52/11.69        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 11.52/11.69      inference('sup-', [status(thm)], ['53', '60'])).
% 11.52/11.69  thf('62', plain,
% 11.52/11.69      (![X0 : $i]:
% 11.52/11.69         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 11.52/11.69      inference('sup-', [status(thm)], ['23', '25'])).
% 11.52/11.69  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('64', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('65', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('66', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(redefinition_k2_relset_1, axiom,
% 11.52/11.69    (![A:$i,B:$i,C:$i]:
% 11.52/11.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.52/11.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 11.52/11.69  thf('67', plain,
% 11.52/11.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 11.52/11.69         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 11.52/11.69          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 11.52/11.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 11.52/11.69  thf('68', plain,
% 11.52/11.69      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 11.52/11.69      inference('sup-', [status(thm)], ['66', '67'])).
% 11.52/11.69  thf('69', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(cc2_funct_2, axiom,
% 11.52/11.69    (![A:$i,B:$i,C:$i]:
% 11.52/11.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.52/11.69       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 11.52/11.69         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 11.52/11.69  thf('70', plain,
% 11.52/11.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 11.52/11.69         (~ (v1_funct_1 @ X18)
% 11.52/11.69          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 11.52/11.69          | (v2_funct_2 @ X18 @ X20)
% 11.52/11.69          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 11.52/11.69      inference('cnf', [status(esa)], [cc2_funct_2])).
% 11.52/11.69  thf('71', plain,
% 11.52/11.69      (((v2_funct_2 @ sk_B @ sk_A)
% 11.52/11.69        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.52/11.69        | ~ (v1_funct_1 @ sk_B))),
% 11.52/11.69      inference('sup-', [status(thm)], ['69', '70'])).
% 11.52/11.69  thf('72', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('74', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 11.52/11.69      inference('demod', [status(thm)], ['71', '72', '73'])).
% 11.52/11.69  thf(d3_funct_2, axiom,
% 11.52/11.69    (![A:$i,B:$i]:
% 11.52/11.69     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 11.52/11.69       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 11.52/11.69  thf('75', plain,
% 11.52/11.69      (![X21 : $i, X22 : $i]:
% 11.52/11.69         (~ (v2_funct_2 @ X22 @ X21)
% 11.52/11.69          | ((k2_relat_1 @ X22) = (X21))
% 11.52/11.69          | ~ (v5_relat_1 @ X22 @ X21)
% 11.52/11.69          | ~ (v1_relat_1 @ X22))),
% 11.52/11.69      inference('cnf', [status(esa)], [d3_funct_2])).
% 11.52/11.69  thf('76', plain,
% 11.52/11.69      ((~ (v1_relat_1 @ sk_B)
% 11.52/11.69        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 11.52/11.69        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 11.52/11.69      inference('sup-', [status(thm)], ['74', '75'])).
% 11.52/11.69  thf('77', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(cc1_relset_1, axiom,
% 11.52/11.69    (![A:$i,B:$i,C:$i]:
% 11.52/11.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.52/11.69       ( v1_relat_1 @ C ) ))).
% 11.52/11.69  thf('78', plain,
% 11.52/11.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 11.52/11.69         ((v1_relat_1 @ X2)
% 11.52/11.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 11.52/11.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.52/11.69  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 11.52/11.69      inference('sup-', [status(thm)], ['77', '78'])).
% 11.52/11.69  thf('80', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf(cc2_relset_1, axiom,
% 11.52/11.69    (![A:$i,B:$i,C:$i]:
% 11.52/11.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.52/11.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 11.52/11.69  thf('81', plain,
% 11.52/11.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.52/11.69         ((v5_relat_1 @ X5 @ X7)
% 11.52/11.69          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 11.52/11.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 11.52/11.69  thf('82', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 11.52/11.69      inference('sup-', [status(thm)], ['80', '81'])).
% 11.52/11.69  thf('83', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 11.52/11.69      inference('demod', [status(thm)], ['76', '79', '82'])).
% 11.52/11.69  thf('84', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 11.52/11.69      inference('demod', [status(thm)], ['68', '83'])).
% 11.52/11.69  thf('85', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('86', plain,
% 11.52/11.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 11.52/11.69         (~ (v1_funct_1 @ X18)
% 11.52/11.69          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 11.52/11.69          | (v2_funct_1 @ X18)
% 11.52/11.69          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 11.52/11.69      inference('cnf', [status(esa)], [cc2_funct_2])).
% 11.52/11.69  thf('87', plain,
% 11.52/11.69      (((v2_funct_1 @ sk_B)
% 11.52/11.69        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.52/11.69        | ~ (v1_funct_1 @ sk_B))),
% 11.52/11.69      inference('sup-', [status(thm)], ['85', '86'])).
% 11.52/11.69  thf('88', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('89', plain, ((v1_funct_1 @ sk_B)),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('90', plain, ((v2_funct_1 @ sk_B)),
% 11.52/11.69      inference('demod', [status(thm)], ['87', '88', '89'])).
% 11.52/11.69  thf('91', plain,
% 11.52/11.69      ((((sk_A) != (sk_A))
% 11.52/11.69        | ((sk_A) = (k1_xboole_0))
% 11.52/11.69        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 11.52/11.69      inference('demod', [status(thm)],
% 11.52/11.69                ['61', '62', '63', '64', '65', '84', '90'])).
% 11.52/11.69  thf('92', plain,
% 11.52/11.69      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 11.52/11.69      inference('simplify', [status(thm)], ['91'])).
% 11.52/11.69  thf('93', plain,
% 11.52/11.69      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('94', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 11.52/11.69      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 11.52/11.69  thf('95', plain,
% 11.52/11.69      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 11.52/11.69      inference('demod', [status(thm)], ['93', '94'])).
% 11.52/11.69  thf('96', plain,
% 11.52/11.69      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 11.52/11.69      inference('sup-', [status(thm)], ['92', '95'])).
% 11.52/11.69  thf('97', plain,
% 11.52/11.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.52/11.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.52/11.69  thf('98', plain,
% 11.52/11.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 11.52/11.69         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 11.52/11.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 11.52/11.69      inference('simplify', [status(thm)], ['24'])).
% 11.52/11.69  thf('99', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 11.52/11.69      inference('sup-', [status(thm)], ['97', '98'])).
% 11.52/11.69  thf('100', plain, (((sk_A) = (k1_xboole_0))),
% 11.52/11.69      inference('demod', [status(thm)], ['96', '99'])).
% 11.52/11.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 11.52/11.69  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.52/11.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.52/11.69  thf('102', plain, ($false),
% 11.52/11.69      inference('demod', [status(thm)], ['38', '100', '101'])).
% 11.52/11.69  
% 11.52/11.69  % SZS output end Refutation
% 11.52/11.69  
% 11.54/11.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
