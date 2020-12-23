%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gprHbR1Vcq

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:03 EST 2020

% Result     : Theorem 12.36s
% Output     : Refutation 12.36s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 217 expanded)
%              Number of leaves         :   39 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          : 1369 (4713 expanded)
%              Number of equality atoms :   52 (  59 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','12'])).

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

thf('14',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['19','28'])).

thf('30',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('44',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38
        = ( k2_funct_1 @ X41 ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X39 @ X39 @ X40 @ X41 @ X38 ) @ ( k6_partfun1 @ X40 ) )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('47',plain,(
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
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
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
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
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
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
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
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_2 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('64',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_2 @ X21 @ X20 )
      | ( ( k2_relat_1 @ X21 )
        = X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('71',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('75',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['69','72','75'])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['61','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','55','56','57','58','77','83'])).

thf('85',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_funct_2 @ X33 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','93'])).

thf('95',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('98',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['95','98'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['29','99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gprHbR1Vcq
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 12.36/12.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.36/12.55  % Solved by: fo/fo7.sh
% 12.36/12.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.36/12.55  % done 7581 iterations in 12.092s
% 12.36/12.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.36/12.55  % SZS output start Refutation
% 12.36/12.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 12.36/12.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.36/12.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 12.36/12.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.36/12.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.36/12.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.36/12.55  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 12.36/12.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 12.36/12.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.36/12.55  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 12.36/12.55  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 12.36/12.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.36/12.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.36/12.55  thf(sk_A_type, type, sk_A: $i).
% 12.36/12.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 12.36/12.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 12.36/12.55  thf(sk_C_type, type, sk_C: $i).
% 12.36/12.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 12.36/12.55  thf(sk_B_type, type, sk_B: $i).
% 12.36/12.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 12.36/12.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 12.36/12.55  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 12.36/12.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.36/12.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.36/12.55  thf(l13_xboole_0, axiom,
% 12.36/12.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 12.36/12.55  thf('0', plain,
% 12.36/12.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.36/12.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.36/12.55  thf('1', plain,
% 12.36/12.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.36/12.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.36/12.55  thf(dt_k6_partfun1, axiom,
% 12.36/12.55    (![A:$i]:
% 12.36/12.55     ( ( m1_subset_1 @
% 12.36/12.55         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 12.36/12.55       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 12.36/12.55  thf('2', plain,
% 12.36/12.55      (![X31 : $i]:
% 12.36/12.55         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 12.36/12.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 12.36/12.55      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 12.36/12.55  thf(cc4_relset_1, axiom,
% 12.36/12.55    (![A:$i,B:$i]:
% 12.36/12.55     ( ( v1_xboole_0 @ A ) =>
% 12.36/12.55       ( ![C:$i]:
% 12.36/12.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 12.36/12.55           ( v1_xboole_0 @ C ) ) ) ))).
% 12.36/12.55  thf('3', plain,
% 12.36/12.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.36/12.55         (~ (v1_xboole_0 @ X7)
% 12.36/12.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 12.36/12.55          | (v1_xboole_0 @ X8))),
% 12.36/12.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 12.36/12.55  thf('4', plain,
% 12.36/12.55      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 12.36/12.55      inference('sup-', [status(thm)], ['2', '3'])).
% 12.36/12.55  thf('5', plain,
% 12.36/12.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.36/12.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.36/12.55  thf('6', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         (~ (v1_xboole_0 @ X0) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 12.36/12.55      inference('sup-', [status(thm)], ['4', '5'])).
% 12.36/12.55  thf('7', plain,
% 12.36/12.55      (![X31 : $i]:
% 12.36/12.55         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 12.36/12.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 12.36/12.55      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 12.36/12.55  thf('8', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 12.36/12.55          | ~ (v1_xboole_0 @ X0))),
% 12.36/12.55      inference('sup+', [status(thm)], ['6', '7'])).
% 12.36/12.55  thf(redefinition_r2_relset_1, axiom,
% 12.36/12.55    (![A:$i,B:$i,C:$i,D:$i]:
% 12.36/12.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.36/12.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.36/12.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 12.36/12.55  thf('9', plain,
% 12.36/12.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 12.36/12.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 12.36/12.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 12.36/12.55          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 12.36/12.55          | ((X13) != (X16)))),
% 12.36/12.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 12.36/12.55  thf('10', plain,
% 12.36/12.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 12.36/12.55         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 12.36/12.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 12.36/12.55      inference('simplify', [status(thm)], ['9'])).
% 12.36/12.55  thf('11', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         (~ (v1_xboole_0 @ X0)
% 12.36/12.55          | (r2_relset_1 @ X0 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 12.36/12.55      inference('sup-', [status(thm)], ['8', '10'])).
% 12.36/12.55  thf('12', plain,
% 12.36/12.55      (![X0 : $i, X1 : $i]:
% 12.36/12.55         ((r2_relset_1 @ X1 @ X1 @ X0 @ k1_xboole_0)
% 12.36/12.55          | ~ (v1_xboole_0 @ X0)
% 12.36/12.55          | ~ (v1_xboole_0 @ X1))),
% 12.36/12.55      inference('sup+', [status(thm)], ['1', '11'])).
% 12.36/12.55  thf('13', plain,
% 12.36/12.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.36/12.55         ((r2_relset_1 @ X2 @ X2 @ X1 @ X0)
% 12.36/12.55          | ~ (v1_xboole_0 @ X0)
% 12.36/12.55          | ~ (v1_xboole_0 @ X2)
% 12.36/12.55          | ~ (v1_xboole_0 @ X1))),
% 12.36/12.55      inference('sup+', [status(thm)], ['0', '12'])).
% 12.36/12.55  thf(t87_funct_2, conjecture,
% 12.36/12.55    (![A:$i,B:$i]:
% 12.36/12.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.36/12.55         ( v3_funct_2 @ B @ A @ A ) & 
% 12.36/12.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.36/12.55       ( ![C:$i]:
% 12.36/12.55         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 12.36/12.55             ( v3_funct_2 @ C @ A @ A ) & 
% 12.36/12.55             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.36/12.55           ( ( r2_relset_1 @
% 12.36/12.55               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 12.36/12.55               ( k6_partfun1 @ A ) ) =>
% 12.36/12.55             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 12.36/12.55  thf(zf_stmt_0, negated_conjecture,
% 12.36/12.55    (~( ![A:$i,B:$i]:
% 12.36/12.55        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.36/12.55            ( v3_funct_2 @ B @ A @ A ) & 
% 12.36/12.55            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.36/12.55          ( ![C:$i]:
% 12.36/12.55            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 12.36/12.55                ( v3_funct_2 @ C @ A @ A ) & 
% 12.36/12.55                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.36/12.55              ( ( r2_relset_1 @
% 12.36/12.55                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 12.36/12.55                  ( k6_partfun1 @ A ) ) =>
% 12.36/12.55                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 12.36/12.55    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 12.36/12.55  thf('14', plain,
% 12.36/12.55      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('15', plain,
% 12.36/12.55      ((~ (v1_xboole_0 @ sk_C)
% 12.36/12.55        | ~ (v1_xboole_0 @ sk_A)
% 12.36/12.55        | ~ (v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 12.36/12.55      inference('sup-', [status(thm)], ['13', '14'])).
% 12.36/12.55  thf('16', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('17', plain,
% 12.36/12.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.36/12.55         (~ (v1_xboole_0 @ X7)
% 12.36/12.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 12.36/12.55          | (v1_xboole_0 @ X8))),
% 12.36/12.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 12.36/12.55  thf('18', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 12.36/12.55      inference('sup-', [status(thm)], ['16', '17'])).
% 12.36/12.55  thf('19', plain,
% 12.36/12.55      ((~ (v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 12.36/12.55      inference('clc', [status(thm)], ['15', '18'])).
% 12.36/12.55  thf('20', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(dt_k2_funct_2, axiom,
% 12.36/12.55    (![A:$i,B:$i]:
% 12.36/12.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.36/12.55         ( v3_funct_2 @ B @ A @ A ) & 
% 12.36/12.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.36/12.55       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 12.36/12.55         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 12.36/12.55         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 12.36/12.55         ( m1_subset_1 @
% 12.36/12.55           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 12.36/12.55  thf('21', plain,
% 12.36/12.55      (![X28 : $i, X29 : $i]:
% 12.36/12.55         ((m1_subset_1 @ (k2_funct_2 @ X28 @ X29) @ 
% 12.36/12.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 12.36/12.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 12.36/12.55          | ~ (v3_funct_2 @ X29 @ X28 @ X28)
% 12.36/12.55          | ~ (v1_funct_2 @ X29 @ X28 @ X28)
% 12.36/12.55          | ~ (v1_funct_1 @ X29))),
% 12.36/12.55      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 12.36/12.55  thf('22', plain,
% 12.36/12.55      ((~ (v1_funct_1 @ sk_B)
% 12.36/12.55        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 12.36/12.55        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 12.36/12.55        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 12.36/12.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 12.36/12.55      inference('sup-', [status(thm)], ['20', '21'])).
% 12.36/12.55  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('24', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('26', plain,
% 12.36/12.55      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 12.36/12.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 12.36/12.55  thf('27', plain,
% 12.36/12.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.36/12.55         (~ (v1_xboole_0 @ X7)
% 12.36/12.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 12.36/12.55          | (v1_xboole_0 @ X8))),
% 12.36/12.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 12.36/12.55  thf('28', plain,
% 12.36/12.55      (((v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 12.36/12.55      inference('sup-', [status(thm)], ['26', '27'])).
% 12.36/12.55  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 12.36/12.55      inference('clc', [status(thm)], ['19', '28'])).
% 12.36/12.55  thf('30', plain,
% 12.36/12.55      ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.36/12.55        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 12.36/12.55        (k6_partfun1 @ sk_A))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('31', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('32', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(dt_k1_partfun1, axiom,
% 12.36/12.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.36/12.55     ( ( ( v1_funct_1 @ E ) & 
% 12.36/12.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.36/12.55         ( v1_funct_1 @ F ) & 
% 12.36/12.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 12.36/12.55       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 12.36/12.55         ( m1_subset_1 @
% 12.36/12.55           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 12.36/12.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 12.36/12.55  thf('33', plain,
% 12.36/12.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 12.36/12.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 12.36/12.55          | ~ (v1_funct_1 @ X22)
% 12.36/12.55          | ~ (v1_funct_1 @ X25)
% 12.36/12.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 12.36/12.55          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 12.36/12.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 12.36/12.55      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 12.36/12.55  thf('34', plain,
% 12.36/12.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.36/12.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 12.36/12.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 12.36/12.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 12.36/12.55          | ~ (v1_funct_1 @ X1)
% 12.36/12.55          | ~ (v1_funct_1 @ sk_B))),
% 12.36/12.55      inference('sup-', [status(thm)], ['32', '33'])).
% 12.36/12.55  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('36', plain,
% 12.36/12.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.36/12.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 12.36/12.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 12.36/12.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 12.36/12.55          | ~ (v1_funct_1 @ X1))),
% 12.36/12.55      inference('demod', [status(thm)], ['34', '35'])).
% 12.36/12.55  thf('37', plain,
% 12.36/12.55      ((~ (v1_funct_1 @ sk_C)
% 12.36/12.55        | (m1_subset_1 @ 
% 12.36/12.55           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 12.36/12.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 12.36/12.55      inference('sup-', [status(thm)], ['31', '36'])).
% 12.36/12.55  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('39', plain,
% 12.36/12.55      ((m1_subset_1 @ 
% 12.36/12.55        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 12.36/12.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('demod', [status(thm)], ['37', '38'])).
% 12.36/12.55  thf('40', plain,
% 12.36/12.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 12.36/12.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 12.36/12.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 12.36/12.55          | ((X13) = (X16))
% 12.36/12.55          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 12.36/12.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 12.36/12.55  thf('41', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.36/12.55             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 12.36/12.55          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 12.36/12.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 12.36/12.55      inference('sup-', [status(thm)], ['39', '40'])).
% 12.36/12.55  thf('42', plain,
% 12.36/12.55      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 12.36/12.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 12.36/12.55        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 12.36/12.55            = (k6_partfun1 @ sk_A)))),
% 12.36/12.55      inference('sup-', [status(thm)], ['30', '41'])).
% 12.36/12.55  thf('43', plain,
% 12.36/12.55      (![X31 : $i]:
% 12.36/12.55         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 12.36/12.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 12.36/12.55      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 12.36/12.55  thf('44', plain,
% 12.36/12.55      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 12.36/12.55         = (k6_partfun1 @ sk_A))),
% 12.36/12.55      inference('demod', [status(thm)], ['42', '43'])).
% 12.36/12.55  thf('45', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(t36_funct_2, axiom,
% 12.36/12.55    (![A:$i,B:$i,C:$i]:
% 12.36/12.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.36/12.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.36/12.55       ( ![D:$i]:
% 12.36/12.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 12.36/12.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 12.36/12.55           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 12.36/12.55               ( r2_relset_1 @
% 12.36/12.55                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 12.36/12.55                 ( k6_partfun1 @ A ) ) & 
% 12.36/12.55               ( v2_funct_1 @ C ) ) =>
% 12.36/12.55             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 12.36/12.55               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 12.36/12.55  thf('46', plain,
% 12.36/12.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 12.36/12.55         (~ (v1_funct_1 @ X38)
% 12.36/12.55          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 12.36/12.55          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 12.36/12.55          | ((X38) = (k2_funct_1 @ X41))
% 12.36/12.55          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 12.36/12.55               (k1_partfun1 @ X40 @ X39 @ X39 @ X40 @ X41 @ X38) @ 
% 12.36/12.55               (k6_partfun1 @ X40))
% 12.36/12.55          | ((X39) = (k1_xboole_0))
% 12.36/12.55          | ((X40) = (k1_xboole_0))
% 12.36/12.55          | ~ (v2_funct_1 @ X41)
% 12.36/12.55          | ((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 12.36/12.55          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 12.36/12.55          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 12.36/12.55          | ~ (v1_funct_1 @ X41))),
% 12.36/12.55      inference('cnf', [status(esa)], [t36_funct_2])).
% 12.36/12.55  thf('47', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         (~ (v1_funct_1 @ X0)
% 12.36/12.55          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 12.36/12.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 12.36/12.55          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 12.36/12.55          | ~ (v2_funct_1 @ X0)
% 12.36/12.55          | ((sk_A) = (k1_xboole_0))
% 12.36/12.55          | ((sk_A) = (k1_xboole_0))
% 12.36/12.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.36/12.55               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 12.36/12.55               (k6_partfun1 @ sk_A))
% 12.36/12.55          | ((sk_C) = (k2_funct_1 @ X0))
% 12.36/12.55          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 12.36/12.55          | ~ (v1_funct_1 @ sk_C))),
% 12.36/12.55      inference('sup-', [status(thm)], ['45', '46'])).
% 12.36/12.55  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('50', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         (~ (v1_funct_1 @ X0)
% 12.36/12.55          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 12.36/12.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 12.36/12.55          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 12.36/12.55          | ~ (v2_funct_1 @ X0)
% 12.36/12.55          | ((sk_A) = (k1_xboole_0))
% 12.36/12.55          | ((sk_A) = (k1_xboole_0))
% 12.36/12.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.36/12.55               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 12.36/12.55               (k6_partfun1 @ sk_A))
% 12.36/12.55          | ((sk_C) = (k2_funct_1 @ X0)))),
% 12.36/12.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 12.36/12.55  thf('51', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         (((sk_C) = (k2_funct_1 @ X0))
% 12.36/12.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.36/12.55               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 12.36/12.55               (k6_partfun1 @ sk_A))
% 12.36/12.55          | ((sk_A) = (k1_xboole_0))
% 12.36/12.55          | ~ (v2_funct_1 @ X0)
% 12.36/12.55          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 12.36/12.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 12.36/12.55          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 12.36/12.55          | ~ (v1_funct_1 @ X0))),
% 12.36/12.55      inference('simplify', [status(thm)], ['50'])).
% 12.36/12.55  thf('52', plain,
% 12.36/12.55      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 12.36/12.55           (k6_partfun1 @ sk_A))
% 12.36/12.55        | ~ (v1_funct_1 @ sk_B)
% 12.36/12.55        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 12.36/12.55        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 12.36/12.55        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 12.36/12.55        | ~ (v2_funct_1 @ sk_B)
% 12.36/12.55        | ((sk_A) = (k1_xboole_0))
% 12.36/12.55        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 12.36/12.55      inference('sup-', [status(thm)], ['44', '51'])).
% 12.36/12.55  thf('53', plain,
% 12.36/12.55      (![X31 : $i]:
% 12.36/12.55         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 12.36/12.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 12.36/12.55      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 12.36/12.55  thf('54', plain,
% 12.36/12.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 12.36/12.55         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 12.36/12.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 12.36/12.55      inference('simplify', [status(thm)], ['9'])).
% 12.36/12.55  thf('55', plain,
% 12.36/12.55      (![X0 : $i]:
% 12.36/12.55         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 12.36/12.55      inference('sup-', [status(thm)], ['53', '54'])).
% 12.36/12.55  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('57', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('58', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('59', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(redefinition_k2_relset_1, axiom,
% 12.36/12.55    (![A:$i,B:$i,C:$i]:
% 12.36/12.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.36/12.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 12.36/12.55  thf('60', plain,
% 12.36/12.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.36/12.55         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 12.36/12.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 12.36/12.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 12.36/12.55  thf('61', plain,
% 12.36/12.55      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 12.36/12.55      inference('sup-', [status(thm)], ['59', '60'])).
% 12.36/12.55  thf('62', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(cc2_funct_2, axiom,
% 12.36/12.55    (![A:$i,B:$i,C:$i]:
% 12.36/12.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.36/12.55       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 12.36/12.55         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 12.36/12.55  thf('63', plain,
% 12.36/12.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.36/12.55         (~ (v1_funct_1 @ X17)
% 12.36/12.55          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 12.36/12.55          | (v2_funct_2 @ X17 @ X19)
% 12.36/12.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 12.36/12.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 12.36/12.55  thf('64', plain,
% 12.36/12.55      (((v2_funct_2 @ sk_B @ sk_A)
% 12.36/12.55        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 12.36/12.55        | ~ (v1_funct_1 @ sk_B))),
% 12.36/12.55      inference('sup-', [status(thm)], ['62', '63'])).
% 12.36/12.55  thf('65', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('67', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 12.36/12.55      inference('demod', [status(thm)], ['64', '65', '66'])).
% 12.36/12.55  thf(d3_funct_2, axiom,
% 12.36/12.55    (![A:$i,B:$i]:
% 12.36/12.55     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 12.36/12.55       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 12.36/12.55  thf('68', plain,
% 12.36/12.55      (![X20 : $i, X21 : $i]:
% 12.36/12.55         (~ (v2_funct_2 @ X21 @ X20)
% 12.36/12.55          | ((k2_relat_1 @ X21) = (X20))
% 12.36/12.55          | ~ (v5_relat_1 @ X21 @ X20)
% 12.36/12.55          | ~ (v1_relat_1 @ X21))),
% 12.36/12.55      inference('cnf', [status(esa)], [d3_funct_2])).
% 12.36/12.55  thf('69', plain,
% 12.36/12.55      ((~ (v1_relat_1 @ sk_B)
% 12.36/12.55        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 12.36/12.55        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 12.36/12.55      inference('sup-', [status(thm)], ['67', '68'])).
% 12.36/12.55  thf('70', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(cc1_relset_1, axiom,
% 12.36/12.55    (![A:$i,B:$i,C:$i]:
% 12.36/12.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.36/12.55       ( v1_relat_1 @ C ) ))).
% 12.36/12.55  thf('71', plain,
% 12.36/12.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 12.36/12.55         ((v1_relat_1 @ X1)
% 12.36/12.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 12.36/12.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.36/12.55  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 12.36/12.55      inference('sup-', [status(thm)], ['70', '71'])).
% 12.36/12.55  thf('73', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(cc2_relset_1, axiom,
% 12.36/12.55    (![A:$i,B:$i,C:$i]:
% 12.36/12.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.36/12.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 12.36/12.55  thf('74', plain,
% 12.36/12.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 12.36/12.55         ((v5_relat_1 @ X4 @ X6)
% 12.36/12.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 12.36/12.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 12.36/12.55  thf('75', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 12.36/12.55      inference('sup-', [status(thm)], ['73', '74'])).
% 12.36/12.55  thf('76', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 12.36/12.55      inference('demod', [status(thm)], ['69', '72', '75'])).
% 12.36/12.55  thf('77', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 12.36/12.55      inference('demod', [status(thm)], ['61', '76'])).
% 12.36/12.55  thf('78', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('79', plain,
% 12.36/12.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.36/12.55         (~ (v1_funct_1 @ X17)
% 12.36/12.55          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 12.36/12.55          | (v2_funct_1 @ X17)
% 12.36/12.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 12.36/12.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 12.36/12.55  thf('80', plain,
% 12.36/12.55      (((v2_funct_1 @ sk_B)
% 12.36/12.55        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 12.36/12.55        | ~ (v1_funct_1 @ sk_B))),
% 12.36/12.55      inference('sup-', [status(thm)], ['78', '79'])).
% 12.36/12.55  thf('81', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('83', plain, ((v2_funct_1 @ sk_B)),
% 12.36/12.55      inference('demod', [status(thm)], ['80', '81', '82'])).
% 12.36/12.55  thf('84', plain,
% 12.36/12.55      ((((sk_A) != (sk_A))
% 12.36/12.55        | ((sk_A) = (k1_xboole_0))
% 12.36/12.55        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 12.36/12.55      inference('demod', [status(thm)],
% 12.36/12.55                ['52', '55', '56', '57', '58', '77', '83'])).
% 12.36/12.55  thf('85', plain,
% 12.36/12.55      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 12.36/12.55      inference('simplify', [status(thm)], ['84'])).
% 12.36/12.55  thf('86', plain,
% 12.36/12.55      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('87', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf(redefinition_k2_funct_2, axiom,
% 12.36/12.55    (![A:$i,B:$i]:
% 12.36/12.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.36/12.55         ( v3_funct_2 @ B @ A @ A ) & 
% 12.36/12.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.36/12.55       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 12.36/12.55  thf('88', plain,
% 12.36/12.55      (![X32 : $i, X33 : $i]:
% 12.36/12.55         (((k2_funct_2 @ X33 @ X32) = (k2_funct_1 @ X32))
% 12.36/12.55          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 12.36/12.55          | ~ (v3_funct_2 @ X32 @ X33 @ X33)
% 12.36/12.55          | ~ (v1_funct_2 @ X32 @ X33 @ X33)
% 12.36/12.55          | ~ (v1_funct_1 @ X32))),
% 12.36/12.55      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 12.36/12.55  thf('89', plain,
% 12.36/12.55      ((~ (v1_funct_1 @ sk_B)
% 12.36/12.55        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 12.36/12.55        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 12.36/12.55        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 12.36/12.55      inference('sup-', [status(thm)], ['87', '88'])).
% 12.36/12.55  thf('90', plain, ((v1_funct_1 @ sk_B)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('91', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('92', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('93', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 12.36/12.55      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 12.36/12.55  thf('94', plain,
% 12.36/12.55      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 12.36/12.55      inference('demod', [status(thm)], ['86', '93'])).
% 12.36/12.55  thf('95', plain,
% 12.36/12.55      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 12.36/12.55      inference('sup-', [status(thm)], ['85', '94'])).
% 12.36/12.55  thf('96', plain,
% 12.36/12.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.36/12.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.36/12.55  thf('97', plain,
% 12.36/12.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 12.36/12.55         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 12.36/12.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 12.36/12.55      inference('simplify', [status(thm)], ['9'])).
% 12.36/12.55  thf('98', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 12.36/12.55      inference('sup-', [status(thm)], ['96', '97'])).
% 12.36/12.55  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 12.36/12.55      inference('demod', [status(thm)], ['95', '98'])).
% 12.36/12.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 12.36/12.55  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.36/12.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.36/12.55  thf('101', plain, ($false),
% 12.36/12.55      inference('demod', [status(thm)], ['29', '99', '100'])).
% 12.36/12.55  
% 12.36/12.55  % SZS output end Refutation
% 12.36/12.55  
% 12.36/12.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
