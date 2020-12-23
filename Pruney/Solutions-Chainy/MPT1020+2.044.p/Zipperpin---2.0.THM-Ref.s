%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u45sJsTFBr

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:07 EST 2020

% Result     : Theorem 21.43s
% Output     : Refutation 21.43s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 330 expanded)
%              Number of leaves         :   39 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          : 1673 (7442 expanded)
%              Number of equality atoms :   87 ( 122 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('5',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('7',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

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

thf('16',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_funct_2 @ X32 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','40'])).

thf('42',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('44',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( X47
        = ( k2_funct_1 @ X50 ) )
      | ~ ( r2_relset_1 @ X49 @ X49 @ ( k1_partfun1 @ X49 @ X48 @ X48 @ X49 @ X50 @ X47 ) @ ( k6_partfun1 @ X49 ) )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X49 @ X48 @ X50 )
       != X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('61',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( X47
        = ( k2_funct_1 @ X50 ) )
      | ~ ( r2_relset_1 @ X49 @ X49 @ ( k1_partfun1 @ X49 @ X48 @ X48 @ X49 @ X50 @ X47 ) @ ( k6_relat_1 @ X49 ) )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X49 @ X48 @ X50 )
       != X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('70',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('80',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','71','72','73','74','77','83'])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf('87',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X41 @ X40 @ ( k1_partfun1 @ X41 @ X39 @ X39 @ X40 @ X42 @ X38 ) )
       != X40 )
      | ( ( k2_relset_1 @ X41 @ X39 @ X42 )
        = X39 )
      | ( X40 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X39 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t28_funct_2])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_relset_1 @ X1 @ sk_A @ X0 )
        = sk_A )
      | ( ( k2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) )
       != sk_A )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('91',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_relset_1 @ X1 @ sk_A @ X0 )
        = sk_A )
      | ( ( k2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) )
       != sk_A ) ) ),
    inference(demod,[status(thm)],['88','94','95','96'])).

thf('98',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) )
     != sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['85','97'])).

thf('99',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('100',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('102',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( sk_A != sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','103','104','105','106','107'])).

thf('109',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['84','109'])).

thf('111',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('112',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('115',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['41','116','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u45sJsTFBr
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:36:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 21.43/21.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 21.43/21.62  % Solved by: fo/fo7.sh
% 21.43/21.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.43/21.62  % done 9786 iterations in 21.163s
% 21.43/21.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 21.43/21.62  % SZS output start Refutation
% 21.43/21.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.43/21.62  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 21.43/21.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 21.43/21.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 21.43/21.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.43/21.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.43/21.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 21.43/21.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 21.43/21.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.43/21.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 21.43/21.62  thf(sk_A_type, type, sk_A: $i).
% 21.43/21.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 21.43/21.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 21.43/21.62  thf(sk_B_type, type, sk_B: $i).
% 21.43/21.62  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 21.43/21.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 21.43/21.62  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 21.43/21.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 21.43/21.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 21.43/21.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.43/21.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.43/21.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.43/21.62  thf(sk_C_type, type, sk_C: $i).
% 21.43/21.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 21.43/21.62  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 21.43/21.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 21.43/21.62  thf(t8_boole, axiom,
% 21.43/21.62    (![A:$i,B:$i]:
% 21.43/21.62     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 21.43/21.62  thf('1', plain,
% 21.43/21.62      (![X0 : $i, X1 : $i]:
% 21.43/21.62         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 21.43/21.62      inference('cnf', [status(esa)], [t8_boole])).
% 21.43/21.62  thf('2', plain,
% 21.43/21.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 21.43/21.62      inference('sup-', [status(thm)], ['0', '1'])).
% 21.43/21.62  thf('3', plain,
% 21.43/21.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 21.43/21.62      inference('sup-', [status(thm)], ['0', '1'])).
% 21.43/21.62  thf('4', plain,
% 21.43/21.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 21.43/21.62      inference('sup-', [status(thm)], ['0', '1'])).
% 21.43/21.62  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 21.43/21.62  thf('5', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 21.43/21.62      inference('cnf', [status(esa)], [t81_relat_1])).
% 21.43/21.62  thf('6', plain,
% 21.43/21.62      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 21.43/21.62      inference('sup+', [status(thm)], ['4', '5'])).
% 21.43/21.62  thf(dt_k6_partfun1, axiom,
% 21.43/21.62    (![A:$i]:
% 21.43/21.62     ( ( m1_subset_1 @
% 21.43/21.62         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 21.43/21.62       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 21.43/21.62  thf('7', plain,
% 21.43/21.62      (![X30 : $i]:
% 21.43/21.62         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 21.43/21.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 21.43/21.62      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 21.43/21.62  thf(redefinition_k6_partfun1, axiom,
% 21.43/21.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 21.43/21.62  thf('8', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 21.43/21.62  thf('9', plain,
% 21.43/21.62      (![X30 : $i]:
% 21.43/21.62         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 21.43/21.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 21.43/21.62      inference('demod', [status(thm)], ['7', '8'])).
% 21.43/21.62  thf('10', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 21.43/21.62          | ~ (v1_xboole_0 @ X0))),
% 21.43/21.62      inference('sup+', [status(thm)], ['6', '9'])).
% 21.43/21.62  thf(redefinition_r2_relset_1, axiom,
% 21.43/21.62    (![A:$i,B:$i,C:$i,D:$i]:
% 21.43/21.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.43/21.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.43/21.62       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 21.43/21.62  thf('11', plain,
% 21.43/21.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 21.43/21.62         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 21.43/21.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 21.43/21.62          | (r2_relset_1 @ X15 @ X16 @ X14 @ X17)
% 21.43/21.62          | ((X14) != (X17)))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 21.43/21.62  thf('12', plain,
% 21.43/21.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 21.43/21.62         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 21.43/21.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 21.43/21.62      inference('simplify', [status(thm)], ['11'])).
% 21.43/21.62  thf('13', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         (~ (v1_xboole_0 @ X0)
% 21.43/21.62          | (r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 21.43/21.62      inference('sup-', [status(thm)], ['10', '12'])).
% 21.43/21.62  thf('14', plain,
% 21.43/21.62      (![X0 : $i, X1 : $i]:
% 21.43/21.62         ((r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0)
% 21.43/21.62          | ~ (v1_xboole_0 @ X0)
% 21.43/21.62          | ~ (v1_xboole_0 @ X1))),
% 21.43/21.62      inference('sup+', [status(thm)], ['3', '13'])).
% 21.43/21.62  thf('15', plain,
% 21.43/21.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.43/21.62         ((r2_relset_1 @ X2 @ X2 @ X1 @ X0)
% 21.43/21.62          | ~ (v1_xboole_0 @ X0)
% 21.43/21.62          | ~ (v1_xboole_0 @ X2)
% 21.43/21.62          | ~ (v1_xboole_0 @ X1))),
% 21.43/21.62      inference('sup+', [status(thm)], ['2', '14'])).
% 21.43/21.62  thf(t87_funct_2, conjecture,
% 21.43/21.62    (![A:$i,B:$i]:
% 21.43/21.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 21.43/21.62         ( v3_funct_2 @ B @ A @ A ) & 
% 21.43/21.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 21.43/21.62       ( ![C:$i]:
% 21.43/21.62         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 21.43/21.62             ( v3_funct_2 @ C @ A @ A ) & 
% 21.43/21.62             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 21.43/21.62           ( ( r2_relset_1 @
% 21.43/21.62               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 21.43/21.62               ( k6_partfun1 @ A ) ) =>
% 21.43/21.62             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 21.43/21.62  thf(zf_stmt_0, negated_conjecture,
% 21.43/21.62    (~( ![A:$i,B:$i]:
% 21.43/21.62        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 21.43/21.62            ( v3_funct_2 @ B @ A @ A ) & 
% 21.43/21.62            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 21.43/21.62          ( ![C:$i]:
% 21.43/21.62            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 21.43/21.62                ( v3_funct_2 @ C @ A @ A ) & 
% 21.43/21.62                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 21.43/21.62              ( ( r2_relset_1 @
% 21.43/21.62                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 21.43/21.62                  ( k6_partfun1 @ A ) ) =>
% 21.43/21.62                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 21.43/21.62    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 21.43/21.62  thf('16', plain,
% 21.43/21.62      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('17', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(redefinition_k2_funct_2, axiom,
% 21.43/21.62    (![A:$i,B:$i]:
% 21.43/21.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 21.43/21.62         ( v3_funct_2 @ B @ A @ A ) & 
% 21.43/21.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 21.43/21.62       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 21.43/21.62  thf('18', plain,
% 21.43/21.62      (![X31 : $i, X32 : $i]:
% 21.43/21.62         (((k2_funct_2 @ X32 @ X31) = (k2_funct_1 @ X31))
% 21.43/21.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 21.43/21.62          | ~ (v3_funct_2 @ X31 @ X32 @ X32)
% 21.43/21.62          | ~ (v1_funct_2 @ X31 @ X32 @ X32)
% 21.43/21.62          | ~ (v1_funct_1 @ X31))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 21.43/21.62  thf('19', plain,
% 21.43/21.62      ((~ (v1_funct_1 @ sk_B)
% 21.43/21.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 21.43/21.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 21.43/21.62        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 21.43/21.62      inference('sup-', [status(thm)], ['17', '18'])).
% 21.43/21.62  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('21', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('22', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('23', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 21.43/21.62      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 21.43/21.62  thf('24', plain,
% 21.43/21.62      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 21.43/21.62      inference('demod', [status(thm)], ['16', '23'])).
% 21.43/21.62  thf('25', plain,
% 21.43/21.62      ((~ (v1_xboole_0 @ sk_C)
% 21.43/21.62        | ~ (v1_xboole_0 @ sk_A)
% 21.43/21.62        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 21.43/21.62      inference('sup-', [status(thm)], ['15', '24'])).
% 21.43/21.62  thf('26', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(cc3_relset_1, axiom,
% 21.43/21.62    (![A:$i,B:$i]:
% 21.43/21.62     ( ( v1_xboole_0 @ A ) =>
% 21.43/21.62       ( ![C:$i]:
% 21.43/21.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.43/21.62           ( v1_xboole_0 @ C ) ) ) ))).
% 21.43/21.62  thf('27', plain,
% 21.43/21.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 21.43/21.62         (~ (v1_xboole_0 @ X8)
% 21.43/21.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 21.43/21.62          | (v1_xboole_0 @ X9))),
% 21.43/21.62      inference('cnf', [status(esa)], [cc3_relset_1])).
% 21.43/21.62  thf('28', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 21.43/21.62      inference('sup-', [status(thm)], ['26', '27'])).
% 21.43/21.62  thf('29', plain,
% 21.43/21.62      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 21.43/21.62      inference('clc', [status(thm)], ['25', '28'])).
% 21.43/21.62  thf('30', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(dt_k2_funct_2, axiom,
% 21.43/21.62    (![A:$i,B:$i]:
% 21.43/21.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 21.43/21.62         ( v3_funct_2 @ B @ A @ A ) & 
% 21.43/21.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 21.43/21.62       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 21.43/21.62         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 21.43/21.62         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 21.43/21.62         ( m1_subset_1 @
% 21.43/21.62           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 21.43/21.62  thf('31', plain,
% 21.43/21.62      (![X27 : $i, X28 : $i]:
% 21.43/21.62         ((m1_subset_1 @ (k2_funct_2 @ X27 @ X28) @ 
% 21.43/21.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 21.43/21.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 21.43/21.62          | ~ (v3_funct_2 @ X28 @ X27 @ X27)
% 21.43/21.62          | ~ (v1_funct_2 @ X28 @ X27 @ X27)
% 21.43/21.62          | ~ (v1_funct_1 @ X28))),
% 21.43/21.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 21.43/21.62  thf('32', plain,
% 21.43/21.62      ((~ (v1_funct_1 @ sk_B)
% 21.43/21.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 21.43/21.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 21.43/21.62        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 21.43/21.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 21.43/21.62      inference('sup-', [status(thm)], ['30', '31'])).
% 21.43/21.62  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('34', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('35', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('36', plain,
% 21.43/21.62      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 21.43/21.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 21.43/21.62  thf('37', plain,
% 21.43/21.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 21.43/21.62         (~ (v1_xboole_0 @ X8)
% 21.43/21.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 21.43/21.62          | (v1_xboole_0 @ X9))),
% 21.43/21.62      inference('cnf', [status(esa)], [cc3_relset_1])).
% 21.43/21.62  thf('38', plain,
% 21.43/21.62      (((v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 21.43/21.62      inference('sup-', [status(thm)], ['36', '37'])).
% 21.43/21.62  thf('39', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 21.43/21.62      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 21.43/21.62  thf('40', plain,
% 21.43/21.62      (((v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 21.43/21.62      inference('demod', [status(thm)], ['38', '39'])).
% 21.43/21.62  thf('41', plain, (~ (v1_xboole_0 @ sk_A)),
% 21.43/21.62      inference('clc', [status(thm)], ['29', '40'])).
% 21.43/21.62  thf('42', plain,
% 21.43/21.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 21.43/21.62        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 21.43/21.62        (k6_partfun1 @ sk_A))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('43', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 21.43/21.62  thf('44', plain,
% 21.43/21.62      ((r2_relset_1 @ sk_A @ sk_A @ 
% 21.43/21.62        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 21.43/21.62        (k6_relat_1 @ sk_A))),
% 21.43/21.62      inference('demod', [status(thm)], ['42', '43'])).
% 21.43/21.62  thf('45', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('46', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(dt_k1_partfun1, axiom,
% 21.43/21.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 21.43/21.62     ( ( ( v1_funct_1 @ E ) & 
% 21.43/21.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.43/21.62         ( v1_funct_1 @ F ) & 
% 21.43/21.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 21.43/21.62       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 21.43/21.62         ( m1_subset_1 @
% 21.43/21.62           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 21.43/21.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 21.43/21.62  thf('47', plain,
% 21.43/21.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 21.43/21.62         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 21.43/21.62          | ~ (v1_funct_1 @ X21)
% 21.43/21.62          | ~ (v1_funct_1 @ X24)
% 21.43/21.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 21.43/21.62          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 21.43/21.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 21.43/21.62      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 21.43/21.62  thf('48', plain,
% 21.43/21.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.43/21.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 21.43/21.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 21.43/21.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 21.43/21.62          | ~ (v1_funct_1 @ X1)
% 21.43/21.62          | ~ (v1_funct_1 @ sk_B))),
% 21.43/21.62      inference('sup-', [status(thm)], ['46', '47'])).
% 21.43/21.62  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('50', plain,
% 21.43/21.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.43/21.62         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 21.43/21.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 21.43/21.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 21.43/21.62          | ~ (v1_funct_1 @ X1))),
% 21.43/21.62      inference('demod', [status(thm)], ['48', '49'])).
% 21.43/21.62  thf('51', plain,
% 21.43/21.62      ((~ (v1_funct_1 @ sk_C)
% 21.43/21.62        | (m1_subset_1 @ 
% 21.43/21.62           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 21.43/21.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 21.43/21.62      inference('sup-', [status(thm)], ['45', '50'])).
% 21.43/21.62  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('53', plain,
% 21.43/21.62      ((m1_subset_1 @ 
% 21.43/21.62        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 21.43/21.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('demod', [status(thm)], ['51', '52'])).
% 21.43/21.62  thf('54', plain,
% 21.43/21.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 21.43/21.62         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 21.43/21.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 21.43/21.62          | ((X14) = (X17))
% 21.43/21.62          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 21.43/21.62  thf('55', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 21.43/21.62             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 21.43/21.62          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 21.43/21.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 21.43/21.62      inference('sup-', [status(thm)], ['53', '54'])).
% 21.43/21.62  thf('56', plain,
% 21.43/21.62      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 21.43/21.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 21.43/21.62        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 21.43/21.62            = (k6_relat_1 @ sk_A)))),
% 21.43/21.62      inference('sup-', [status(thm)], ['44', '55'])).
% 21.43/21.62  thf('57', plain,
% 21.43/21.62      (![X30 : $i]:
% 21.43/21.62         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 21.43/21.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 21.43/21.62      inference('demod', [status(thm)], ['7', '8'])).
% 21.43/21.62  thf('58', plain,
% 21.43/21.62      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 21.43/21.62         = (k6_relat_1 @ sk_A))),
% 21.43/21.62      inference('demod', [status(thm)], ['56', '57'])).
% 21.43/21.62  thf('59', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(t36_funct_2, axiom,
% 21.43/21.62    (![A:$i,B:$i,C:$i]:
% 21.43/21.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.43/21.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.43/21.62       ( ![D:$i]:
% 21.43/21.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 21.43/21.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 21.43/21.62           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 21.43/21.62               ( r2_relset_1 @
% 21.43/21.62                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 21.43/21.62                 ( k6_partfun1 @ A ) ) & 
% 21.43/21.62               ( v2_funct_1 @ C ) ) =>
% 21.43/21.62             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 21.43/21.62               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 21.43/21.62  thf('60', plain,
% 21.43/21.62      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X47)
% 21.43/21.62          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 21.43/21.62          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 21.43/21.62          | ((X47) = (k2_funct_1 @ X50))
% 21.43/21.62          | ~ (r2_relset_1 @ X49 @ X49 @ 
% 21.43/21.62               (k1_partfun1 @ X49 @ X48 @ X48 @ X49 @ X50 @ X47) @ 
% 21.43/21.62               (k6_partfun1 @ X49))
% 21.43/21.62          | ((X48) = (k1_xboole_0))
% 21.43/21.62          | ((X49) = (k1_xboole_0))
% 21.43/21.62          | ~ (v2_funct_1 @ X50)
% 21.43/21.62          | ((k2_relset_1 @ X49 @ X48 @ X50) != (X48))
% 21.43/21.62          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 21.43/21.62          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 21.43/21.62          | ~ (v1_funct_1 @ X50))),
% 21.43/21.62      inference('cnf', [status(esa)], [t36_funct_2])).
% 21.43/21.62  thf('61', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 21.43/21.62  thf('62', plain,
% 21.43/21.62      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X47)
% 21.43/21.62          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 21.43/21.62          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 21.43/21.62          | ((X47) = (k2_funct_1 @ X50))
% 21.43/21.62          | ~ (r2_relset_1 @ X49 @ X49 @ 
% 21.43/21.62               (k1_partfun1 @ X49 @ X48 @ X48 @ X49 @ X50 @ X47) @ 
% 21.43/21.62               (k6_relat_1 @ X49))
% 21.43/21.62          | ((X48) = (k1_xboole_0))
% 21.43/21.62          | ((X49) = (k1_xboole_0))
% 21.43/21.62          | ~ (v2_funct_1 @ X50)
% 21.43/21.62          | ((k2_relset_1 @ X49 @ X48 @ X50) != (X48))
% 21.43/21.62          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 21.43/21.62          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 21.43/21.62          | ~ (v1_funct_1 @ X50))),
% 21.43/21.62      inference('demod', [status(thm)], ['60', '61'])).
% 21.43/21.62  thf('63', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X0)
% 21.43/21.62          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 21.43/21.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 21.43/21.62          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 21.43/21.62          | ~ (v2_funct_1 @ X0)
% 21.43/21.62          | ((sk_A) = (k1_xboole_0))
% 21.43/21.62          | ((sk_A) = (k1_xboole_0))
% 21.43/21.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 21.43/21.62               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 21.43/21.62               (k6_relat_1 @ sk_A))
% 21.43/21.62          | ((sk_C) = (k2_funct_1 @ X0))
% 21.43/21.62          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 21.43/21.62          | ~ (v1_funct_1 @ sk_C))),
% 21.43/21.62      inference('sup-', [status(thm)], ['59', '62'])).
% 21.43/21.62  thf('64', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('66', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X0)
% 21.43/21.62          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 21.43/21.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 21.43/21.62          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 21.43/21.62          | ~ (v2_funct_1 @ X0)
% 21.43/21.62          | ((sk_A) = (k1_xboole_0))
% 21.43/21.62          | ((sk_A) = (k1_xboole_0))
% 21.43/21.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 21.43/21.62               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 21.43/21.62               (k6_relat_1 @ sk_A))
% 21.43/21.62          | ((sk_C) = (k2_funct_1 @ X0)))),
% 21.43/21.62      inference('demod', [status(thm)], ['63', '64', '65'])).
% 21.43/21.62  thf('67', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         (((sk_C) = (k2_funct_1 @ X0))
% 21.43/21.62          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 21.43/21.62               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 21.43/21.62               (k6_relat_1 @ sk_A))
% 21.43/21.62          | ((sk_A) = (k1_xboole_0))
% 21.43/21.62          | ~ (v2_funct_1 @ X0)
% 21.43/21.62          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 21.43/21.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 21.43/21.62          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 21.43/21.62          | ~ (v1_funct_1 @ X0))),
% 21.43/21.62      inference('simplify', [status(thm)], ['66'])).
% 21.43/21.62  thf('68', plain,
% 21.43/21.62      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 21.43/21.62           (k6_relat_1 @ sk_A))
% 21.43/21.62        | ~ (v1_funct_1 @ sk_B)
% 21.43/21.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 21.43/21.62        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 21.43/21.62        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 21.43/21.62        | ~ (v2_funct_1 @ sk_B)
% 21.43/21.62        | ((sk_A) = (k1_xboole_0))
% 21.43/21.62        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 21.43/21.62      inference('sup-', [status(thm)], ['58', '67'])).
% 21.43/21.62  thf('69', plain,
% 21.43/21.62      (![X30 : $i]:
% 21.43/21.62         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 21.43/21.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 21.43/21.62      inference('demod', [status(thm)], ['7', '8'])).
% 21.43/21.62  thf('70', plain,
% 21.43/21.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 21.43/21.62         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 21.43/21.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 21.43/21.62      inference('simplify', [status(thm)], ['11'])).
% 21.43/21.62  thf('71', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 21.43/21.62      inference('sup-', [status(thm)], ['69', '70'])).
% 21.43/21.62  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('73', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('74', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('75', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(redefinition_k2_relset_1, axiom,
% 21.43/21.62    (![A:$i,B:$i,C:$i]:
% 21.43/21.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.43/21.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 21.43/21.62  thf('76', plain,
% 21.43/21.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 21.43/21.62         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 21.43/21.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.43/21.62  thf('77', plain,
% 21.43/21.62      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 21.43/21.62      inference('sup-', [status(thm)], ['75', '76'])).
% 21.43/21.62  thf('78', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(cc2_funct_2, axiom,
% 21.43/21.62    (![A:$i,B:$i,C:$i]:
% 21.43/21.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.43/21.62       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 21.43/21.62         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 21.43/21.62  thf('79', plain,
% 21.43/21.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X18)
% 21.43/21.62          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 21.43/21.62          | (v2_funct_1 @ X18)
% 21.43/21.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 21.43/21.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 21.43/21.62  thf('80', plain,
% 21.43/21.62      (((v2_funct_1 @ sk_B)
% 21.43/21.62        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 21.43/21.62        | ~ (v1_funct_1 @ sk_B))),
% 21.43/21.62      inference('sup-', [status(thm)], ['78', '79'])).
% 21.43/21.62  thf('81', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('83', plain, ((v2_funct_1 @ sk_B)),
% 21.43/21.62      inference('demod', [status(thm)], ['80', '81', '82'])).
% 21.43/21.62  thf('84', plain,
% 21.43/21.62      ((((k2_relat_1 @ sk_B) != (sk_A))
% 21.43/21.62        | ((sk_A) = (k1_xboole_0))
% 21.43/21.62        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 21.43/21.62      inference('demod', [status(thm)],
% 21.43/21.62                ['68', '71', '72', '73', '74', '77', '83'])).
% 21.43/21.62  thf('85', plain,
% 21.43/21.62      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 21.43/21.62         = (k6_relat_1 @ sk_A))),
% 21.43/21.62      inference('demod', [status(thm)], ['56', '57'])).
% 21.43/21.62  thf('86', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf(t28_funct_2, axiom,
% 21.43/21.62    (![A:$i,B:$i,C:$i,D:$i]:
% 21.43/21.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.43/21.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.43/21.62       ( ![E:$i]:
% 21.43/21.62         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 21.43/21.62             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 21.43/21.62           ( ( ( ( k2_relset_1 @
% 21.43/21.62                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 21.43/21.62                 ( C ) ) & 
% 21.43/21.62               ( v2_funct_1 @ E ) ) =>
% 21.43/21.62             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 21.43/21.62               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 21.43/21.62  thf('87', plain,
% 21.43/21.62      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X38)
% 21.43/21.62          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 21.43/21.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 21.43/21.62          | ~ (v2_funct_1 @ X38)
% 21.43/21.62          | ((k2_relset_1 @ X41 @ X40 @ 
% 21.43/21.62              (k1_partfun1 @ X41 @ X39 @ X39 @ X40 @ X42 @ X38)) != (X40))
% 21.43/21.62          | ((k2_relset_1 @ X41 @ X39 @ X42) = (X39))
% 21.43/21.62          | ((X40) = (k1_xboole_0))
% 21.43/21.62          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 21.43/21.62          | ~ (v1_funct_2 @ X42 @ X41 @ X39)
% 21.43/21.62          | ~ (v1_funct_1 @ X42))),
% 21.43/21.62      inference('cnf', [status(esa)], [t28_funct_2])).
% 21.43/21.62  thf('88', plain,
% 21.43/21.62      (![X0 : $i, X1 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X0)
% 21.43/21.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 21.43/21.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 21.43/21.62          | ((sk_A) = (k1_xboole_0))
% 21.43/21.62          | ((k2_relset_1 @ X1 @ sk_A @ X0) = (sk_A))
% 21.43/21.62          | ((k2_relset_1 @ X1 @ sk_A @ 
% 21.43/21.62              (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C)) != (
% 21.43/21.62              sk_A))
% 21.43/21.62          | ~ (v2_funct_1 @ sk_C)
% 21.43/21.62          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 21.43/21.62          | ~ (v1_funct_1 @ sk_C))),
% 21.43/21.62      inference('sup-', [status(thm)], ['86', '87'])).
% 21.43/21.62  thf('89', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('90', plain,
% 21.43/21.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X18)
% 21.43/21.62          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 21.43/21.62          | (v2_funct_1 @ X18)
% 21.43/21.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 21.43/21.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 21.43/21.62  thf('91', plain,
% 21.43/21.62      (((v2_funct_1 @ sk_C)
% 21.43/21.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 21.43/21.62        | ~ (v1_funct_1 @ sk_C))),
% 21.43/21.62      inference('sup-', [status(thm)], ['89', '90'])).
% 21.43/21.62  thf('92', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 21.43/21.62      inference('demod', [status(thm)], ['91', '92', '93'])).
% 21.43/21.62  thf('95', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('97', plain,
% 21.43/21.62      (![X0 : $i, X1 : $i]:
% 21.43/21.62         (~ (v1_funct_1 @ X0)
% 21.43/21.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 21.43/21.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 21.43/21.62          | ((sk_A) = (k1_xboole_0))
% 21.43/21.62          | ((k2_relset_1 @ X1 @ sk_A @ X0) = (sk_A))
% 21.43/21.62          | ((k2_relset_1 @ X1 @ sk_A @ 
% 21.43/21.62              (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_C)) != (
% 21.43/21.62              sk_A)))),
% 21.43/21.62      inference('demod', [status(thm)], ['88', '94', '95', '96'])).
% 21.43/21.62  thf('98', plain,
% 21.43/21.62      ((((k2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A)) != (sk_A))
% 21.43/21.62        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))
% 21.43/21.62        | ((sk_A) = (k1_xboole_0))
% 21.43/21.62        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 21.43/21.62        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 21.43/21.62        | ~ (v1_funct_1 @ sk_B))),
% 21.43/21.62      inference('sup-', [status(thm)], ['85', '97'])).
% 21.43/21.62  thf('99', plain,
% 21.43/21.62      (![X30 : $i]:
% 21.43/21.62         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 21.43/21.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 21.43/21.62      inference('demod', [status(thm)], ['7', '8'])).
% 21.43/21.62  thf('100', plain,
% 21.43/21.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 21.43/21.62         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 21.43/21.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 21.43/21.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.43/21.62  thf('101', plain,
% 21.43/21.62      (![X0 : $i]:
% 21.43/21.62         ((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 21.43/21.62           = (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 21.43/21.62      inference('sup-', [status(thm)], ['99', '100'])).
% 21.43/21.62  thf(t71_relat_1, axiom,
% 21.43/21.62    (![A:$i]:
% 21.43/21.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 21.43/21.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 21.43/21.62  thf('102', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 21.43/21.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 21.43/21.62  thf('103', plain,
% 21.43/21.62      (![X0 : $i]: ((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0)) = (X0))),
% 21.43/21.62      inference('demod', [status(thm)], ['101', '102'])).
% 21.43/21.62  thf('104', plain,
% 21.43/21.62      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 21.43/21.62      inference('sup-', [status(thm)], ['75', '76'])).
% 21.43/21.62  thf('105', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('106', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('107', plain, ((v1_funct_1 @ sk_B)),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('108', plain,
% 21.43/21.62      ((((sk_A) != (sk_A))
% 21.43/21.62        | ((k2_relat_1 @ sk_B) = (sk_A))
% 21.43/21.62        | ((sk_A) = (k1_xboole_0)))),
% 21.43/21.62      inference('demod', [status(thm)],
% 21.43/21.62                ['98', '103', '104', '105', '106', '107'])).
% 21.43/21.62  thf('109', plain,
% 21.43/21.62      ((((sk_A) = (k1_xboole_0)) | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 21.43/21.62      inference('simplify', [status(thm)], ['108'])).
% 21.43/21.62  thf('110', plain,
% 21.43/21.62      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 21.43/21.62      inference('clc', [status(thm)], ['84', '109'])).
% 21.43/21.62  thf('111', plain,
% 21.43/21.62      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 21.43/21.62      inference('demod', [status(thm)], ['16', '23'])).
% 21.43/21.62  thf('112', plain,
% 21.43/21.62      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 21.43/21.62      inference('sup-', [status(thm)], ['110', '111'])).
% 21.43/21.62  thf('113', plain,
% 21.43/21.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.43/21.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.43/21.62  thf('114', plain,
% 21.43/21.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 21.43/21.62         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 21.43/21.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 21.43/21.62      inference('simplify', [status(thm)], ['11'])).
% 21.43/21.62  thf('115', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 21.43/21.62      inference('sup-', [status(thm)], ['113', '114'])).
% 21.43/21.62  thf('116', plain, (((sk_A) = (k1_xboole_0))),
% 21.43/21.62      inference('demod', [status(thm)], ['112', '115'])).
% 21.43/21.62  thf('117', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 21.43/21.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 21.43/21.62  thf('118', plain, ($false),
% 21.43/21.62      inference('demod', [status(thm)], ['41', '116', '117'])).
% 21.43/21.62  
% 21.43/21.62  % SZS output end Refutation
% 21.43/21.62  
% 21.43/21.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
