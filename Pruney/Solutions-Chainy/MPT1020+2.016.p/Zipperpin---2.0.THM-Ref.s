%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.szEwlf04dH

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:03 EST 2020

% Result     : Theorem 11.04s
% Output     : Refutation 11.04s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 273 expanded)
%              Number of leaves         :   41 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          : 1408 (5215 expanded)
%              Number of equality atoms :   63 (  90 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X2 ) )
      = ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('15',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

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

thf('22',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_funct_2 @ X33 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
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

thf('59',plain,(
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

thf('60',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( X39
        = ( k2_funct_1 @ X42 ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X40 @ X40 @ X41 @ X42 @ X39 ) @ ( k6_relat_1 @ X41 ) )
      | ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
       != X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
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
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
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
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
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
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('73',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_2 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('77',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['77','78','79'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_2 @ X23 @ X22 )
      | ( ( k2_relat_1 @ X23 )
        = X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('87',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('88',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['82','85','88'])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['74','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('93',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','90','96'])).

thf('98',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('100',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('103',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['40','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.szEwlf04dH
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 11.04/11.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.04/11.24  % Solved by: fo/fo7.sh
% 11.04/11.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.04/11.24  % done 5111 iterations in 10.791s
% 11.04/11.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.04/11.24  % SZS output start Refutation
% 11.04/11.24  thf(sk_B_type, type, sk_B: $i).
% 11.04/11.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 11.04/11.24  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 11.04/11.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.04/11.24  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 11.04/11.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.04/11.24  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 11.04/11.24  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 11.04/11.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.04/11.24  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 11.04/11.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.04/11.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 11.04/11.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 11.04/11.24  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 11.04/11.24  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 11.04/11.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.04/11.24  thf(sk_A_type, type, sk_A: $i).
% 11.04/11.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 11.04/11.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.04/11.24  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 11.04/11.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.04/11.24  thf(sk_C_type, type, sk_C: $i).
% 11.04/11.24  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 11.04/11.24  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 11.04/11.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.04/11.24  thf(dt_k6_partfun1, axiom,
% 11.04/11.24    (![A:$i]:
% 11.04/11.24     ( ( m1_subset_1 @
% 11.04/11.24         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 11.04/11.24       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 11.04/11.24  thf('0', plain,
% 11.04/11.24      (![X31 : $i]:
% 11.04/11.24         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 11.04/11.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 11.04/11.24      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 11.04/11.24  thf(redefinition_k6_partfun1, axiom,
% 11.04/11.24    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 11.04/11.24  thf('1', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 11.04/11.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 11.04/11.24  thf('2', plain,
% 11.04/11.24      (![X31 : $i]:
% 11.04/11.24         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 11.04/11.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 11.04/11.24      inference('demod', [status(thm)], ['0', '1'])).
% 11.04/11.24  thf(cc3_relset_1, axiom,
% 11.04/11.24    (![A:$i,B:$i]:
% 11.04/11.24     ( ( v1_xboole_0 @ A ) =>
% 11.04/11.24       ( ![C:$i]:
% 11.04/11.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.04/11.24           ( v1_xboole_0 @ C ) ) ) ))).
% 11.04/11.24  thf('3', plain,
% 11.04/11.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X9)
% 11.04/11.24          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 11.04/11.24          | (v1_xboole_0 @ X10))),
% 11.04/11.24      inference('cnf', [status(esa)], [cc3_relset_1])).
% 11.04/11.24  thf('4', plain,
% 11.04/11.24      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 11.04/11.24      inference('sup-', [status(thm)], ['2', '3'])).
% 11.04/11.24  thf(t8_boole, axiom,
% 11.04/11.24    (![A:$i,B:$i]:
% 11.04/11.24     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 11.04/11.24  thf('5', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 11.04/11.24      inference('cnf', [status(esa)], [t8_boole])).
% 11.04/11.24  thf('6', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ((k6_relat_1 @ X0) = (X1))
% 11.04/11.24          | ~ (v1_xboole_0 @ X1))),
% 11.04/11.24      inference('sup-', [status(thm)], ['4', '5'])).
% 11.04/11.24  thf(t67_funct_1, axiom,
% 11.04/11.24    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 11.04/11.24  thf('7', plain,
% 11.04/11.24      (![X2 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X2)) = (k6_relat_1 @ X2))),
% 11.04/11.24      inference('cnf', [status(esa)], [t67_funct_1])).
% 11.04/11.24  thf('8', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         (((k2_funct_1 @ X0) = (k6_relat_1 @ X1))
% 11.04/11.24          | ~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ~ (v1_xboole_0 @ X1))),
% 11.04/11.24      inference('sup+', [status(thm)], ['6', '7'])).
% 11.04/11.24  thf('9', plain,
% 11.04/11.24      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 11.04/11.24      inference('sup-', [status(thm)], ['2', '3'])).
% 11.04/11.24  thf('10', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         ((v1_xboole_0 @ (k2_funct_1 @ X0))
% 11.04/11.24          | ~ (v1_xboole_0 @ X1)
% 11.04/11.24          | ~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ~ (v1_xboole_0 @ X1))),
% 11.04/11.24      inference('sup+', [status(thm)], ['8', '9'])).
% 11.04/11.24  thf('11', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ~ (v1_xboole_0 @ X1)
% 11.04/11.24          | (v1_xboole_0 @ (k2_funct_1 @ X0)))),
% 11.04/11.24      inference('simplify', [status(thm)], ['10'])).
% 11.04/11.24  thf('12', plain,
% 11.04/11.24      (![X0 : $i]: ((v1_xboole_0 @ (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 11.04/11.24      inference('condensation', [status(thm)], ['11'])).
% 11.04/11.24  thf('13', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ((k6_relat_1 @ X0) = (X1))
% 11.04/11.24          | ~ (v1_xboole_0 @ X1))),
% 11.04/11.24      inference('sup-', [status(thm)], ['4', '5'])).
% 11.04/11.24  thf('14', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ((k6_relat_1 @ X0) = (X1))
% 11.04/11.24          | ~ (v1_xboole_0 @ X1))),
% 11.04/11.24      inference('sup-', [status(thm)], ['4', '5'])).
% 11.04/11.24  thf('15', plain,
% 11.04/11.24      (![X31 : $i]:
% 11.04/11.24         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 11.04/11.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 11.04/11.24      inference('demod', [status(thm)], ['0', '1'])).
% 11.04/11.24  thf(redefinition_r2_relset_1, axiom,
% 11.04/11.24    (![A:$i,B:$i,C:$i,D:$i]:
% 11.04/11.24     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.04/11.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.04/11.24       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 11.04/11.24  thf('16', plain,
% 11.04/11.24      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 11.04/11.24         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 11.04/11.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 11.04/11.24          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 11.04/11.24          | ((X15) != (X18)))),
% 11.04/11.24      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.04/11.24  thf('17', plain,
% 11.04/11.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 11.04/11.24         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 11.04/11.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 11.04/11.24      inference('simplify', [status(thm)], ['16'])).
% 11.04/11.24  thf('18', plain,
% 11.04/11.24      (![X0 : $i]:
% 11.04/11.24         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 11.04/11.24      inference('sup-', [status(thm)], ['15', '17'])).
% 11.04/11.24  thf('19', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i]:
% 11.04/11.24         ((r2_relset_1 @ X1 @ X1 @ X0 @ (k6_relat_1 @ X1))
% 11.04/11.24          | ~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ~ (v1_xboole_0 @ X1))),
% 11.04/11.24      inference('sup+', [status(thm)], ['14', '18'])).
% 11.04/11.24  thf('20', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.04/11.24         ((r2_relset_1 @ X1 @ X1 @ X2 @ X0)
% 11.04/11.24          | ~ (v1_xboole_0 @ X0)
% 11.04/11.24          | ~ (v1_xboole_0 @ X1)
% 11.04/11.24          | ~ (v1_xboole_0 @ X1)
% 11.04/11.24          | ~ (v1_xboole_0 @ X2))),
% 11.04/11.24      inference('sup+', [status(thm)], ['13', '19'])).
% 11.04/11.24  thf('21', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X2)
% 11.04/11.24          | ~ (v1_xboole_0 @ X1)
% 11.04/11.24          | ~ (v1_xboole_0 @ X0)
% 11.04/11.24          | (r2_relset_1 @ X1 @ X1 @ X2 @ X0))),
% 11.04/11.24      inference('simplify', [status(thm)], ['20'])).
% 11.04/11.24  thf(t87_funct_2, conjecture,
% 11.04/11.24    (![A:$i,B:$i]:
% 11.04/11.24     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.04/11.24         ( v3_funct_2 @ B @ A @ A ) & 
% 11.04/11.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.04/11.24       ( ![C:$i]:
% 11.04/11.24         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 11.04/11.24             ( v3_funct_2 @ C @ A @ A ) & 
% 11.04/11.24             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.04/11.24           ( ( r2_relset_1 @
% 11.04/11.24               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 11.04/11.24               ( k6_partfun1 @ A ) ) =>
% 11.04/11.24             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 11.04/11.24  thf(zf_stmt_0, negated_conjecture,
% 11.04/11.24    (~( ![A:$i,B:$i]:
% 11.04/11.24        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.04/11.24            ( v3_funct_2 @ B @ A @ A ) & 
% 11.04/11.24            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.04/11.24          ( ![C:$i]:
% 11.04/11.24            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 11.04/11.24                ( v3_funct_2 @ C @ A @ A ) & 
% 11.04/11.24                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.04/11.24              ( ( r2_relset_1 @
% 11.04/11.24                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 11.04/11.24                  ( k6_partfun1 @ A ) ) =>
% 11.04/11.24                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 11.04/11.24    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 11.04/11.24  thf('22', plain,
% 11.04/11.24      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('23', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf(redefinition_k2_funct_2, axiom,
% 11.04/11.24    (![A:$i,B:$i]:
% 11.04/11.24     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.04/11.24         ( v3_funct_2 @ B @ A @ A ) & 
% 11.04/11.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.04/11.24       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 11.04/11.24  thf('24', plain,
% 11.04/11.24      (![X32 : $i, X33 : $i]:
% 11.04/11.24         (((k2_funct_2 @ X33 @ X32) = (k2_funct_1 @ X32))
% 11.04/11.24          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 11.04/11.24          | ~ (v3_funct_2 @ X32 @ X33 @ X33)
% 11.04/11.24          | ~ (v1_funct_2 @ X32 @ X33 @ X33)
% 11.04/11.24          | ~ (v1_funct_1 @ X32))),
% 11.04/11.24      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 11.04/11.24  thf('25', plain,
% 11.04/11.24      ((~ (v1_funct_1 @ sk_B)
% 11.04/11.24        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.04/11.24        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.04/11.24        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 11.04/11.24      inference('sup-', [status(thm)], ['23', '24'])).
% 11.04/11.24  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 11.04/11.24      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 11.04/11.24  thf('30', plain,
% 11.04/11.24      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 11.04/11.24      inference('demod', [status(thm)], ['22', '29'])).
% 11.04/11.24  thf('31', plain,
% 11.04/11.24      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B))
% 11.04/11.24        | ~ (v1_xboole_0 @ sk_A)
% 11.04/11.24        | ~ (v1_xboole_0 @ sk_C))),
% 11.04/11.24      inference('sup-', [status(thm)], ['21', '30'])).
% 11.04/11.24  thf('32', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('33', plain,
% 11.04/11.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X9)
% 11.04/11.24          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 11.04/11.24          | (v1_xboole_0 @ X10))),
% 11.04/11.24      inference('cnf', [status(esa)], [cc3_relset_1])).
% 11.04/11.24  thf('34', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 11.04/11.24      inference('sup-', [status(thm)], ['32', '33'])).
% 11.04/11.24  thf('35', plain,
% 11.04/11.24      ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 11.04/11.24      inference('clc', [status(thm)], ['31', '34'])).
% 11.04/11.24  thf('36', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 11.04/11.24      inference('sup-', [status(thm)], ['12', '35'])).
% 11.04/11.24  thf('37', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('38', plain,
% 11.04/11.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 11.04/11.24         (~ (v1_xboole_0 @ X9)
% 11.04/11.24          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 11.04/11.24          | (v1_xboole_0 @ X10))),
% 11.04/11.24      inference('cnf', [status(esa)], [cc3_relset_1])).
% 11.04/11.24  thf('39', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 11.04/11.24      inference('sup-', [status(thm)], ['37', '38'])).
% 11.04/11.24  thf('40', plain, (~ (v1_xboole_0 @ sk_A)),
% 11.04/11.24      inference('clc', [status(thm)], ['36', '39'])).
% 11.04/11.24  thf('41', plain,
% 11.04/11.24      ((r2_relset_1 @ sk_A @ sk_A @ 
% 11.04/11.24        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 11.04/11.24        (k6_partfun1 @ sk_A))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('42', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 11.04/11.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 11.04/11.24  thf('43', plain,
% 11.04/11.24      ((r2_relset_1 @ sk_A @ sk_A @ 
% 11.04/11.24        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 11.04/11.24        (k6_relat_1 @ sk_A))),
% 11.04/11.24      inference('demod', [status(thm)], ['41', '42'])).
% 11.04/11.24  thf('44', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('45', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf(dt_k1_partfun1, axiom,
% 11.04/11.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.04/11.24     ( ( ( v1_funct_1 @ E ) & 
% 11.04/11.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.04/11.24         ( v1_funct_1 @ F ) & 
% 11.04/11.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 11.04/11.24       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 11.04/11.24         ( m1_subset_1 @
% 11.04/11.24           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 11.04/11.24           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 11.04/11.24  thf('46', plain,
% 11.04/11.24      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 11.04/11.24         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 11.04/11.24          | ~ (v1_funct_1 @ X24)
% 11.04/11.24          | ~ (v1_funct_1 @ X27)
% 11.04/11.24          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 11.04/11.24          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 11.04/11.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 11.04/11.24      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 11.04/11.24  thf('47', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.04/11.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 11.04/11.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 11.04/11.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 11.04/11.24          | ~ (v1_funct_1 @ X1)
% 11.04/11.24          | ~ (v1_funct_1 @ sk_B))),
% 11.04/11.24      inference('sup-', [status(thm)], ['45', '46'])).
% 11.04/11.24  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('49', plain,
% 11.04/11.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.04/11.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 11.04/11.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 11.04/11.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 11.04/11.24          | ~ (v1_funct_1 @ X1))),
% 11.04/11.24      inference('demod', [status(thm)], ['47', '48'])).
% 11.04/11.24  thf('50', plain,
% 11.04/11.24      ((~ (v1_funct_1 @ sk_C)
% 11.04/11.24        | (m1_subset_1 @ 
% 11.04/11.24           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 11.04/11.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.04/11.24      inference('sup-', [status(thm)], ['44', '49'])).
% 11.04/11.24  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('52', plain,
% 11.04/11.24      ((m1_subset_1 @ 
% 11.04/11.24        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 11.04/11.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('demod', [status(thm)], ['50', '51'])).
% 11.04/11.24  thf('53', plain,
% 11.04/11.24      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 11.04/11.24         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 11.04/11.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 11.04/11.24          | ((X15) = (X18))
% 11.04/11.24          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 11.04/11.24      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.04/11.24  thf('54', plain,
% 11.04/11.24      (![X0 : $i]:
% 11.04/11.24         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.04/11.24             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 11.04/11.24          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 11.04/11.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.04/11.24      inference('sup-', [status(thm)], ['52', '53'])).
% 11.04/11.24  thf('55', plain,
% 11.04/11.24      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 11.04/11.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.04/11.24        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 11.04/11.24            = (k6_relat_1 @ sk_A)))),
% 11.04/11.24      inference('sup-', [status(thm)], ['43', '54'])).
% 11.04/11.24  thf('56', plain,
% 11.04/11.24      (![X31 : $i]:
% 11.04/11.24         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 11.04/11.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 11.04/11.24      inference('demod', [status(thm)], ['0', '1'])).
% 11.04/11.24  thf('57', plain,
% 11.04/11.24      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 11.04/11.24         = (k6_relat_1 @ sk_A))),
% 11.04/11.24      inference('demod', [status(thm)], ['55', '56'])).
% 11.04/11.24  thf('58', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf(t36_funct_2, axiom,
% 11.04/11.24    (![A:$i,B:$i,C:$i]:
% 11.04/11.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.04/11.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.04/11.24       ( ![D:$i]:
% 11.04/11.24         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 11.04/11.24             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 11.04/11.24           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 11.04/11.24               ( r2_relset_1 @
% 11.04/11.24                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 11.04/11.24                 ( k6_partfun1 @ A ) ) & 
% 11.04/11.24               ( v2_funct_1 @ C ) ) =>
% 11.04/11.24             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 11.04/11.24               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 11.04/11.24  thf('59', plain,
% 11.04/11.24      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 11.04/11.24         (~ (v1_funct_1 @ X39)
% 11.04/11.24          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 11.04/11.24          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 11.04/11.24          | ((X39) = (k2_funct_1 @ X42))
% 11.04/11.24          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 11.04/11.24               (k1_partfun1 @ X41 @ X40 @ X40 @ X41 @ X42 @ X39) @ 
% 11.04/11.24               (k6_partfun1 @ X41))
% 11.04/11.24          | ((X40) = (k1_xboole_0))
% 11.04/11.24          | ((X41) = (k1_xboole_0))
% 11.04/11.24          | ~ (v2_funct_1 @ X42)
% 11.04/11.24          | ((k2_relset_1 @ X41 @ X40 @ X42) != (X40))
% 11.04/11.24          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 11.04/11.24          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 11.04/11.24          | ~ (v1_funct_1 @ X42))),
% 11.04/11.24      inference('cnf', [status(esa)], [t36_funct_2])).
% 11.04/11.24  thf('60', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 11.04/11.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 11.04/11.24  thf('61', plain,
% 11.04/11.24      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 11.04/11.24         (~ (v1_funct_1 @ X39)
% 11.04/11.24          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 11.04/11.24          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 11.04/11.24          | ((X39) = (k2_funct_1 @ X42))
% 11.04/11.24          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 11.04/11.24               (k1_partfun1 @ X41 @ X40 @ X40 @ X41 @ X42 @ X39) @ 
% 11.04/11.24               (k6_relat_1 @ X41))
% 11.04/11.24          | ((X40) = (k1_xboole_0))
% 11.04/11.24          | ((X41) = (k1_xboole_0))
% 11.04/11.24          | ~ (v2_funct_1 @ X42)
% 11.04/11.24          | ((k2_relset_1 @ X41 @ X40 @ X42) != (X40))
% 11.04/11.24          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 11.04/11.24          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 11.04/11.24          | ~ (v1_funct_1 @ X42))),
% 11.04/11.24      inference('demod', [status(thm)], ['59', '60'])).
% 11.04/11.24  thf('62', plain,
% 11.04/11.24      (![X0 : $i]:
% 11.04/11.24         (~ (v1_funct_1 @ X0)
% 11.04/11.24          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.04/11.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.04/11.24          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 11.04/11.24          | ~ (v2_funct_1 @ X0)
% 11.04/11.24          | ((sk_A) = (k1_xboole_0))
% 11.04/11.24          | ((sk_A) = (k1_xboole_0))
% 11.04/11.24          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.04/11.24               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 11.04/11.24               (k6_relat_1 @ sk_A))
% 11.04/11.24          | ((sk_C) = (k2_funct_1 @ X0))
% 11.04/11.24          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 11.04/11.24          | ~ (v1_funct_1 @ sk_C))),
% 11.04/11.24      inference('sup-', [status(thm)], ['58', '61'])).
% 11.04/11.24  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('65', plain,
% 11.04/11.24      (![X0 : $i]:
% 11.04/11.24         (~ (v1_funct_1 @ X0)
% 11.04/11.24          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.04/11.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.04/11.24          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 11.04/11.24          | ~ (v2_funct_1 @ X0)
% 11.04/11.24          | ((sk_A) = (k1_xboole_0))
% 11.04/11.24          | ((sk_A) = (k1_xboole_0))
% 11.04/11.24          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.04/11.24               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 11.04/11.24               (k6_relat_1 @ sk_A))
% 11.04/11.24          | ((sk_C) = (k2_funct_1 @ X0)))),
% 11.04/11.24      inference('demod', [status(thm)], ['62', '63', '64'])).
% 11.04/11.24  thf('66', plain,
% 11.04/11.24      (![X0 : $i]:
% 11.04/11.24         (((sk_C) = (k2_funct_1 @ X0))
% 11.04/11.24          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.04/11.24               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 11.04/11.24               (k6_relat_1 @ sk_A))
% 11.04/11.24          | ((sk_A) = (k1_xboole_0))
% 11.04/11.24          | ~ (v2_funct_1 @ X0)
% 11.04/11.24          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 11.04/11.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.04/11.24          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.04/11.24          | ~ (v1_funct_1 @ X0))),
% 11.04/11.24      inference('simplify', [status(thm)], ['65'])).
% 11.04/11.24  thf('67', plain,
% 11.04/11.24      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 11.04/11.24           (k6_relat_1 @ sk_A))
% 11.04/11.24        | ~ (v1_funct_1 @ sk_B)
% 11.04/11.24        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.04/11.24        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.04/11.24        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 11.04/11.24        | ~ (v2_funct_1 @ sk_B)
% 11.04/11.24        | ((sk_A) = (k1_xboole_0))
% 11.04/11.24        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 11.04/11.24      inference('sup-', [status(thm)], ['57', '66'])).
% 11.04/11.24  thf('68', plain,
% 11.04/11.24      (![X0 : $i]:
% 11.04/11.24         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 11.04/11.24      inference('sup-', [status(thm)], ['15', '17'])).
% 11.04/11.24  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('70', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('71', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('72', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf(redefinition_k2_relset_1, axiom,
% 11.04/11.24    (![A:$i,B:$i,C:$i]:
% 11.04/11.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.04/11.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 11.04/11.24  thf('73', plain,
% 11.04/11.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 11.04/11.24         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 11.04/11.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 11.04/11.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 11.04/11.24  thf('74', plain,
% 11.04/11.24      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 11.04/11.24      inference('sup-', [status(thm)], ['72', '73'])).
% 11.04/11.24  thf('75', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf(cc2_funct_2, axiom,
% 11.04/11.24    (![A:$i,B:$i,C:$i]:
% 11.04/11.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.04/11.24       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 11.04/11.24         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 11.04/11.24  thf('76', plain,
% 11.04/11.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.04/11.24         (~ (v1_funct_1 @ X19)
% 11.04/11.24          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 11.04/11.24          | (v2_funct_2 @ X19 @ X21)
% 11.04/11.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 11.04/11.24      inference('cnf', [status(esa)], [cc2_funct_2])).
% 11.04/11.24  thf('77', plain,
% 11.04/11.24      (((v2_funct_2 @ sk_B @ sk_A)
% 11.04/11.24        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.04/11.24        | ~ (v1_funct_1 @ sk_B))),
% 11.04/11.24      inference('sup-', [status(thm)], ['75', '76'])).
% 11.04/11.24  thf('78', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('80', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 11.04/11.24      inference('demod', [status(thm)], ['77', '78', '79'])).
% 11.04/11.24  thf(d3_funct_2, axiom,
% 11.04/11.24    (![A:$i,B:$i]:
% 11.04/11.24     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 11.04/11.24       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 11.04/11.24  thf('81', plain,
% 11.04/11.24      (![X22 : $i, X23 : $i]:
% 11.04/11.24         (~ (v2_funct_2 @ X23 @ X22)
% 11.04/11.24          | ((k2_relat_1 @ X23) = (X22))
% 11.04/11.24          | ~ (v5_relat_1 @ X23 @ X22)
% 11.04/11.24          | ~ (v1_relat_1 @ X23))),
% 11.04/11.24      inference('cnf', [status(esa)], [d3_funct_2])).
% 11.04/11.24  thf('82', plain,
% 11.04/11.24      ((~ (v1_relat_1 @ sk_B)
% 11.04/11.24        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 11.04/11.24        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 11.04/11.24      inference('sup-', [status(thm)], ['80', '81'])).
% 11.04/11.24  thf('83', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf(cc1_relset_1, axiom,
% 11.04/11.24    (![A:$i,B:$i,C:$i]:
% 11.04/11.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.04/11.24       ( v1_relat_1 @ C ) ))).
% 11.04/11.24  thf('84', plain,
% 11.04/11.24      (![X3 : $i, X4 : $i, X5 : $i]:
% 11.04/11.24         ((v1_relat_1 @ X3)
% 11.04/11.24          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 11.04/11.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.04/11.24  thf('85', plain, ((v1_relat_1 @ sk_B)),
% 11.04/11.24      inference('sup-', [status(thm)], ['83', '84'])).
% 11.04/11.24  thf('86', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf(cc2_relset_1, axiom,
% 11.04/11.24    (![A:$i,B:$i,C:$i]:
% 11.04/11.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.04/11.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 11.04/11.24  thf('87', plain,
% 11.04/11.24      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.04/11.24         ((v5_relat_1 @ X6 @ X8)
% 11.04/11.24          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 11.04/11.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 11.04/11.24  thf('88', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 11.04/11.24      inference('sup-', [status(thm)], ['86', '87'])).
% 11.04/11.24  thf('89', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 11.04/11.24      inference('demod', [status(thm)], ['82', '85', '88'])).
% 11.04/11.24  thf('90', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 11.04/11.24      inference('demod', [status(thm)], ['74', '89'])).
% 11.04/11.24  thf('91', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('92', plain,
% 11.04/11.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.04/11.24         (~ (v1_funct_1 @ X19)
% 11.04/11.24          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 11.04/11.24          | (v2_funct_1 @ X19)
% 11.04/11.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 11.04/11.24      inference('cnf', [status(esa)], [cc2_funct_2])).
% 11.04/11.24  thf('93', plain,
% 11.04/11.24      (((v2_funct_1 @ sk_B)
% 11.04/11.24        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.04/11.24        | ~ (v1_funct_1 @ sk_B))),
% 11.04/11.24      inference('sup-', [status(thm)], ['91', '92'])).
% 11.04/11.24  thf('94', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('95', plain, ((v1_funct_1 @ sk_B)),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('96', plain, ((v2_funct_1 @ sk_B)),
% 11.04/11.24      inference('demod', [status(thm)], ['93', '94', '95'])).
% 11.04/11.24  thf('97', plain,
% 11.04/11.24      ((((sk_A) != (sk_A))
% 11.04/11.24        | ((sk_A) = (k1_xboole_0))
% 11.04/11.24        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 11.04/11.24      inference('demod', [status(thm)],
% 11.04/11.24                ['67', '68', '69', '70', '71', '90', '96'])).
% 11.04/11.24  thf('98', plain,
% 11.04/11.24      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 11.04/11.24      inference('simplify', [status(thm)], ['97'])).
% 11.04/11.24  thf('99', plain,
% 11.04/11.24      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 11.04/11.24      inference('demod', [status(thm)], ['22', '29'])).
% 11.04/11.24  thf('100', plain,
% 11.04/11.24      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 11.04/11.24      inference('sup-', [status(thm)], ['98', '99'])).
% 11.04/11.24  thf('101', plain,
% 11.04/11.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.04/11.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.04/11.24  thf('102', plain,
% 11.04/11.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 11.04/11.24         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 11.04/11.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 11.04/11.24      inference('simplify', [status(thm)], ['16'])).
% 11.04/11.24  thf('103', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 11.04/11.24      inference('sup-', [status(thm)], ['101', '102'])).
% 11.04/11.24  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 11.04/11.24      inference('demod', [status(thm)], ['100', '103'])).
% 11.04/11.24  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 11.04/11.24  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.04/11.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.04/11.24  thf('106', plain, ($false),
% 11.04/11.24      inference('demod', [status(thm)], ['40', '104', '105'])).
% 11.04/11.24  
% 11.04/11.24  % SZS output end Refutation
% 11.04/11.24  
% 11.04/11.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
