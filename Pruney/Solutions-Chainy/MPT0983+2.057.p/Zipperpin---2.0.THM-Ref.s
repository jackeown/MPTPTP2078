%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vB6AQ93vr1

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:10 EST 2020

% Result     : Theorem 2.77s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 471 expanded)
%              Number of leaves         :   38 ( 157 expanded)
%              Depth                    :   17
%              Number of atoms          : 1379 (7356 expanded)
%              Number of equality atoms :   60 ( 158 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('8',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_relset_1 @ X1 @ X0 @ X2 )
        = ( k2_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('29',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != X24 )
      | ( v2_funct_2 @ X25 @ X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('39',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
      | ( v2_funct_2 @ X25 @ ( k2_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('43',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('44',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','47'])).

thf('49',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('51',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('52',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('53',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
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

thf('62',plain,(
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

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    inference(demod,[status(thm)],['67','70','71','72','73'])).

thf('75',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
      | ( v2_funct_2 @ X25 @ ( k2_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('76',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('79',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['67','70','71','72','73'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('82',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['76','79','80','83'])).

thf('85',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('86',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('88',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['59','88'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('94',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('95',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('96',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['90','103'])).

thf('105',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
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

thf('108',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('115',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','116'])).

thf('118',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('119',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
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

thf('121',plain,(
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

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','125'])).

thf('127',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127','128','129','130'])).

thf('132',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['57'])).

thf('133',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('134',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['132','133'])).

thf('135',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['131','134'])).

thf('136',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['104','135','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vB6AQ93vr1
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.77/3.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.77/3.04  % Solved by: fo/fo7.sh
% 2.77/3.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.77/3.04  % done 3346 iterations in 2.582s
% 2.77/3.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.77/3.04  % SZS output start Refutation
% 2.77/3.04  thf(sk_A_type, type, sk_A: $i).
% 2.77/3.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.77/3.04  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.77/3.04  thf(sk_D_type, type, sk_D: $i).
% 2.77/3.04  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.77/3.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.77/3.04  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.77/3.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.77/3.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.77/3.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.77/3.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.77/3.04  thf(sk_B_type, type, sk_B: $i).
% 2.77/3.04  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.77/3.04  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.77/3.04  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.77/3.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.77/3.04  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.77/3.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.77/3.04  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.77/3.04  thf(sk_C_type, type, sk_C: $i).
% 2.77/3.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.77/3.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.77/3.04  thf(t29_funct_2, conjecture,
% 2.77/3.04    (![A:$i,B:$i,C:$i]:
% 2.77/3.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.77/3.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/3.04       ( ![D:$i]:
% 2.77/3.04         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.77/3.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.77/3.04           ( ( r2_relset_1 @
% 2.77/3.04               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.77/3.04               ( k6_partfun1 @ A ) ) =>
% 2.77/3.04             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.77/3.04  thf(zf_stmt_0, negated_conjecture,
% 2.77/3.04    (~( ![A:$i,B:$i,C:$i]:
% 2.77/3.04        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.77/3.04            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/3.04          ( ![D:$i]:
% 2.77/3.04            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.77/3.04                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.77/3.04              ( ( r2_relset_1 @
% 2.77/3.04                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.77/3.04                  ( k6_partfun1 @ A ) ) =>
% 2.77/3.04                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.77/3.04    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.77/3.04  thf('0', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf(redefinition_k2_relset_1, axiom,
% 2.77/3.04    (![A:$i,B:$i,C:$i]:
% 2.77/3.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.77/3.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.77/3.04  thf('1', plain,
% 2.77/3.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.77/3.04         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 2.77/3.04          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.77/3.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.77/3.04  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.77/3.04      inference('sup-', [status(thm)], ['0', '1'])).
% 2.77/3.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.77/3.04  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.77/3.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.77/3.04  thf(t8_boole, axiom,
% 2.77/3.04    (![A:$i,B:$i]:
% 2.77/3.04     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.77/3.04  thf('4', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.77/3.04      inference('cnf', [status(esa)], [t8_boole])).
% 2.77/3.04  thf('5', plain,
% 2.77/3.04      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['3', '4'])).
% 2.77/3.04  thf(t113_zfmisc_1, axiom,
% 2.77/3.04    (![A:$i,B:$i]:
% 2.77/3.04     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.77/3.04       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.77/3.04  thf('6', plain,
% 2.77/3.04      (![X3 : $i, X4 : $i]:
% 2.77/3.04         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.77/3.04      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.77/3.04  thf('7', plain,
% 2.77/3.04      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.77/3.04      inference('simplify', [status(thm)], ['6'])).
% 2.77/3.04  thf(t29_relset_1, axiom,
% 2.77/3.04    (![A:$i]:
% 2.77/3.04     ( m1_subset_1 @
% 2.77/3.04       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.77/3.04  thf('8', plain,
% 2.77/3.04      (![X23 : $i]:
% 2.77/3.04         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 2.77/3.04          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 2.77/3.04      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.77/3.04  thf(redefinition_k6_partfun1, axiom,
% 2.77/3.04    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.77/3.04  thf('9', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.77/3.04      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.77/3.04  thf('10', plain,
% 2.77/3.04      (![X23 : $i]:
% 2.77/3.04         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 2.77/3.04          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 2.77/3.04      inference('demod', [status(thm)], ['8', '9'])).
% 2.77/3.04  thf('11', plain,
% 2.77/3.04      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.77/3.04      inference('sup+', [status(thm)], ['7', '10'])).
% 2.77/3.04  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.77/3.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.77/3.04  thf('13', plain,
% 2.77/3.04      (![X23 : $i]:
% 2.77/3.04         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 2.77/3.04          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 2.77/3.04      inference('demod', [status(thm)], ['8', '9'])).
% 2.77/3.04  thf(cc4_relset_1, axiom,
% 2.77/3.04    (![A:$i,B:$i]:
% 2.77/3.04     ( ( v1_xboole_0 @ A ) =>
% 2.77/3.04       ( ![C:$i]:
% 2.77/3.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.77/3.04           ( v1_xboole_0 @ C ) ) ) ))).
% 2.77/3.04  thf('14', plain,
% 2.77/3.04      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.77/3.04         (~ (v1_xboole_0 @ X13)
% 2.77/3.04          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 2.77/3.04          | (v1_xboole_0 @ X14))),
% 2.77/3.04      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.77/3.04  thf('15', plain,
% 2.77/3.04      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['13', '14'])).
% 2.77/3.04  thf('16', plain,
% 2.77/3.04      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['3', '4'])).
% 2.77/3.04  thf('17', plain,
% 2.77/3.04      (![X0 : $i]:
% 2.77/3.04         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_partfun1 @ X0)))),
% 2.77/3.04      inference('sup-', [status(thm)], ['15', '16'])).
% 2.77/3.04  thf('18', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['12', '17'])).
% 2.77/3.04  thf('19', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.77/3.04      inference('demod', [status(thm)], ['11', '18'])).
% 2.77/3.04  thf('20', plain,
% 2.77/3.04      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['3', '4'])).
% 2.77/3.04  thf('21', plain,
% 2.77/3.04      (![X3 : $i, X4 : $i]:
% 2.77/3.04         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.77/3.04      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.77/3.04  thf('22', plain,
% 2.77/3.04      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.77/3.04      inference('simplify', [status(thm)], ['21'])).
% 2.77/3.04  thf('23', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup+', [status(thm)], ['20', '22'])).
% 2.77/3.04  thf('24', plain,
% 2.77/3.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.77/3.04         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 2.77/3.04          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.77/3.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.77/3.04  thf('25', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.77/3.04         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.77/3.04          | ~ (v1_xboole_0 @ X1)
% 2.77/3.04          | ((k2_relset_1 @ X1 @ X0 @ X2) = (k2_relat_1 @ X2)))),
% 2.77/3.04      inference('sup-', [status(thm)], ['23', '24'])).
% 2.77/3.04  thf('26', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 2.77/3.04          | ~ (v1_xboole_0 @ X1))),
% 2.77/3.04      inference('sup-', [status(thm)], ['19', '25'])).
% 2.77/3.04  thf('27', plain,
% 2.77/3.04      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.77/3.04      inference('simplify', [status(thm)], ['21'])).
% 2.77/3.04  thf('28', plain,
% 2.77/3.04      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['3', '4'])).
% 2.77/3.04  thf('29', plain,
% 2.77/3.04      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.77/3.04      inference('sup+', [status(thm)], ['7', '10'])).
% 2.77/3.04  thf('30', plain,
% 2.77/3.04      (![X0 : $i]:
% 2.77/3.04         ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))
% 2.77/3.04          | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup+', [status(thm)], ['28', '29'])).
% 2.77/3.04  thf('31', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['12', '17'])).
% 2.77/3.04  thf('32', plain,
% 2.77/3.04      (![X0 : $i]:
% 2.77/3.04         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 2.77/3.04          | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('demod', [status(thm)], ['30', '31'])).
% 2.77/3.04  thf(cc2_relset_1, axiom,
% 2.77/3.04    (![A:$i,B:$i,C:$i]:
% 2.77/3.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.77/3.04       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.77/3.04  thf('33', plain,
% 2.77/3.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.77/3.04         ((v5_relat_1 @ X10 @ X12)
% 2.77/3.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.77/3.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.77/3.04  thf('34', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 2.77/3.04          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['32', '33'])).
% 2.77/3.04  thf('35', plain,
% 2.77/3.04      (![X0 : $i]:
% 2.77/3.04         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['27', '34'])).
% 2.77/3.04  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.77/3.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.77/3.04  thf('37', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 2.77/3.04      inference('demod', [status(thm)], ['35', '36'])).
% 2.77/3.04  thf(d3_funct_2, axiom,
% 2.77/3.04    (![A:$i,B:$i]:
% 2.77/3.04     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.77/3.04       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.77/3.04  thf('38', plain,
% 2.77/3.04      (![X24 : $i, X25 : $i]:
% 2.77/3.04         (((k2_relat_1 @ X25) != (X24))
% 2.77/3.04          | (v2_funct_2 @ X25 @ X24)
% 2.77/3.04          | ~ (v5_relat_1 @ X25 @ X24)
% 2.77/3.04          | ~ (v1_relat_1 @ X25))),
% 2.77/3.04      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.77/3.04  thf('39', plain,
% 2.77/3.04      (![X25 : $i]:
% 2.77/3.04         (~ (v1_relat_1 @ X25)
% 2.77/3.04          | ~ (v5_relat_1 @ X25 @ (k2_relat_1 @ X25))
% 2.77/3.04          | (v2_funct_2 @ X25 @ (k2_relat_1 @ X25)))),
% 2.77/3.04      inference('simplify', [status(thm)], ['38'])).
% 2.77/3.04  thf('40', plain,
% 2.77/3.04      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 2.77/3.04        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['37', '39'])).
% 2.77/3.04  thf('41', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['12', '17'])).
% 2.77/3.04  thf(fc4_funct_1, axiom,
% 2.77/3.04    (![A:$i]:
% 2.77/3.04     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.77/3.04       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.77/3.04  thf('42', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 2.77/3.04      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.77/3.04  thf('43', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.77/3.04      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.77/3.04  thf('44', plain, (![X5 : $i]: (v1_relat_1 @ (k6_partfun1 @ X5))),
% 2.77/3.04      inference('demod', [status(thm)], ['42', '43'])).
% 2.77/3.04  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.77/3.04      inference('sup+', [status(thm)], ['41', '44'])).
% 2.77/3.04  thf('46', plain, ((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 2.77/3.04      inference('demod', [status(thm)], ['40', '45'])).
% 2.77/3.04  thf('47', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 2.77/3.04          | ~ (v1_xboole_0 @ X1))),
% 2.77/3.04      inference('sup+', [status(thm)], ['26', '46'])).
% 2.77/3.04  thf('48', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.77/3.04         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X2 @ X1 @ X0))
% 2.77/3.04          | ~ (v1_xboole_0 @ X0)
% 2.77/3.04          | ~ (v1_xboole_0 @ X2))),
% 2.77/3.04      inference('sup+', [status(thm)], ['5', '47'])).
% 2.77/3.04  thf('49', plain,
% 2.77/3.04      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.77/3.04        | ~ (v1_xboole_0 @ sk_A)
% 2.77/3.04        | ~ (v1_xboole_0 @ sk_C))),
% 2.77/3.04      inference('sup+', [status(thm)], ['2', '48'])).
% 2.77/3.04  thf('50', plain,
% 2.77/3.04      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['3', '4'])).
% 2.77/3.04  thf('51', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['12', '17'])).
% 2.77/3.04  thf('52', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 2.77/3.04      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.77/3.04  thf('53', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.77/3.04      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.77/3.04  thf('54', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 2.77/3.04      inference('demod', [status(thm)], ['52', '53'])).
% 2.77/3.04  thf('55', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.77/3.04      inference('sup+', [status(thm)], ['51', '54'])).
% 2.77/3.04  thf('56', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup+', [status(thm)], ['50', '55'])).
% 2.77/3.04  thf('57', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('58', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/3.04      inference('split', [status(esa)], ['57'])).
% 2.77/3.04  thf('59', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/3.04      inference('sup-', [status(thm)], ['56', '58'])).
% 2.77/3.04  thf('60', plain,
% 2.77/3.04      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/3.04        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.77/3.04        (k6_partfun1 @ sk_A))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('61', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf(t24_funct_2, axiom,
% 2.77/3.04    (![A:$i,B:$i,C:$i]:
% 2.77/3.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.77/3.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/3.04       ( ![D:$i]:
% 2.77/3.04         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.77/3.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.77/3.04           ( ( r2_relset_1 @
% 2.77/3.04               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.77/3.04               ( k6_partfun1 @ B ) ) =>
% 2.77/3.04             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.77/3.04  thf('62', plain,
% 2.77/3.04      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.77/3.04         (~ (v1_funct_1 @ X33)
% 2.77/3.04          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.77/3.04          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.77/3.04          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 2.77/3.04               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 2.77/3.04               (k6_partfun1 @ X34))
% 2.77/3.04          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 2.77/3.04          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.77/3.04          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.77/3.04          | ~ (v1_funct_1 @ X36))),
% 2.77/3.04      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.77/3.04  thf('63', plain,
% 2.77/3.04      (![X0 : $i]:
% 2.77/3.04         (~ (v1_funct_1 @ X0)
% 2.77/3.04          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.77/3.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.77/3.04          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.77/3.04          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/3.04               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.77/3.04               (k6_partfun1 @ sk_A))
% 2.77/3.04          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.77/3.04          | ~ (v1_funct_1 @ sk_C))),
% 2.77/3.04      inference('sup-', [status(thm)], ['61', '62'])).
% 2.77/3.04  thf('64', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('66', plain,
% 2.77/3.04      (![X0 : $i]:
% 2.77/3.04         (~ (v1_funct_1 @ X0)
% 2.77/3.04          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.77/3.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.77/3.04          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.77/3.04          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/3.04               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.77/3.04               (k6_partfun1 @ sk_A)))),
% 2.77/3.04      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.77/3.04  thf('67', plain,
% 2.77/3.04      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.77/3.04        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.77/3.04        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.77/3.04        | ~ (v1_funct_1 @ sk_D))),
% 2.77/3.04      inference('sup-', [status(thm)], ['60', '66'])).
% 2.77/3.04  thf('68', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('69', plain,
% 2.77/3.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.77/3.04         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 2.77/3.04          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.77/3.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.77/3.04  thf('70', plain,
% 2.77/3.04      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.77/3.04      inference('sup-', [status(thm)], ['68', '69'])).
% 2.77/3.04  thf('71', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('74', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.77/3.04      inference('demod', [status(thm)], ['67', '70', '71', '72', '73'])).
% 2.77/3.04  thf('75', plain,
% 2.77/3.04      (![X25 : $i]:
% 2.77/3.04         (~ (v1_relat_1 @ X25)
% 2.77/3.04          | ~ (v5_relat_1 @ X25 @ (k2_relat_1 @ X25))
% 2.77/3.04          | (v2_funct_2 @ X25 @ (k2_relat_1 @ X25)))),
% 2.77/3.04      inference('simplify', [status(thm)], ['38'])).
% 2.77/3.04  thf('76', plain,
% 2.77/3.04      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.77/3.04        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.77/3.04        | ~ (v1_relat_1 @ sk_D))),
% 2.77/3.04      inference('sup-', [status(thm)], ['74', '75'])).
% 2.77/3.04  thf('77', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('78', plain,
% 2.77/3.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.77/3.04         ((v5_relat_1 @ X10 @ X12)
% 2.77/3.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.77/3.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.77/3.04  thf('79', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.77/3.04      inference('sup-', [status(thm)], ['77', '78'])).
% 2.77/3.04  thf('80', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.77/3.04      inference('demod', [status(thm)], ['67', '70', '71', '72', '73'])).
% 2.77/3.04  thf('81', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf(cc1_relset_1, axiom,
% 2.77/3.04    (![A:$i,B:$i,C:$i]:
% 2.77/3.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.77/3.04       ( v1_relat_1 @ C ) ))).
% 2.77/3.04  thf('82', plain,
% 2.77/3.04      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.77/3.04         ((v1_relat_1 @ X7)
% 2.77/3.04          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.77/3.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.77/3.04  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 2.77/3.04      inference('sup-', [status(thm)], ['81', '82'])).
% 2.77/3.04  thf('84', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.77/3.04      inference('demod', [status(thm)], ['76', '79', '80', '83'])).
% 2.77/3.04  thf('85', plain,
% 2.77/3.04      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.77/3.04      inference('split', [status(esa)], ['57'])).
% 2.77/3.04  thf('86', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.77/3.04      inference('sup-', [status(thm)], ['84', '85'])).
% 2.77/3.04  thf('87', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.77/3.04      inference('split', [status(esa)], ['57'])).
% 2.77/3.04  thf('88', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.77/3.04      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 2.77/3.04  thf('89', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.77/3.04      inference('simpl_trail', [status(thm)], ['59', '88'])).
% 2.77/3.04  thf('90', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.77/3.04      inference('clc', [status(thm)], ['49', '89'])).
% 2.77/3.04  thf('91', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup+', [status(thm)], ['20', '22'])).
% 2.77/3.04  thf('92', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('93', plain,
% 2.77/3.04      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['3', '4'])).
% 2.77/3.04  thf('94', plain,
% 2.77/3.04      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.77/3.04      inference('simplify', [status(thm)], ['6'])).
% 2.77/3.04  thf('95', plain,
% 2.77/3.04      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.77/3.04         (~ (v1_xboole_0 @ X13)
% 2.77/3.04          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 2.77/3.04          | (v1_xboole_0 @ X14))),
% 2.77/3.04      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.77/3.04  thf('96', plain,
% 2.77/3.04      (![X1 : $i]:
% 2.77/3.04         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.77/3.04          | (v1_xboole_0 @ X1)
% 2.77/3.04          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.77/3.04      inference('sup-', [status(thm)], ['94', '95'])).
% 2.77/3.04  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.77/3.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.77/3.04  thf('98', plain,
% 2.77/3.04      (![X1 : $i]:
% 2.77/3.04         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.77/3.04          | (v1_xboole_0 @ X1))),
% 2.77/3.04      inference('demod', [status(thm)], ['96', '97'])).
% 2.77/3.04  thf('99', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 2.77/3.04          | ~ (v1_xboole_0 @ X0)
% 2.77/3.04          | (v1_xboole_0 @ X1))),
% 2.77/3.04      inference('sup-', [status(thm)], ['93', '98'])).
% 2.77/3.04  thf('100', plain,
% 2.77/3.04      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.77/3.04      inference('sup-', [status(thm)], ['92', '99'])).
% 2.77/3.04  thf('101', plain,
% 2.77/3.04      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.77/3.04        | ~ (v1_xboole_0 @ sk_A)
% 2.77/3.04        | (v1_xboole_0 @ sk_C))),
% 2.77/3.04      inference('sup-', [status(thm)], ['91', '100'])).
% 2.77/3.04  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.77/3.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.77/3.04  thf('103', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 2.77/3.04      inference('demod', [status(thm)], ['101', '102'])).
% 2.77/3.04  thf('104', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.77/3.04      inference('clc', [status(thm)], ['90', '103'])).
% 2.77/3.04  thf('105', plain,
% 2.77/3.04      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/3.04        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.77/3.04        (k6_partfun1 @ sk_A))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('106', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('107', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf(dt_k1_partfun1, axiom,
% 2.77/3.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.77/3.04     ( ( ( v1_funct_1 @ E ) & 
% 2.77/3.04         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.77/3.04         ( v1_funct_1 @ F ) & 
% 2.77/3.04         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.77/3.04       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.77/3.04         ( m1_subset_1 @
% 2.77/3.04           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.77/3.04           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.77/3.04  thf('108', plain,
% 2.77/3.04      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.77/3.04         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.77/3.04          | ~ (v1_funct_1 @ X26)
% 2.77/3.04          | ~ (v1_funct_1 @ X29)
% 2.77/3.04          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.77/3.04          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 2.77/3.04             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 2.77/3.04      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.77/3.04  thf('109', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.77/3.04         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.77/3.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.77/3.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.77/3.04          | ~ (v1_funct_1 @ X1)
% 2.77/3.04          | ~ (v1_funct_1 @ sk_C))),
% 2.77/3.04      inference('sup-', [status(thm)], ['107', '108'])).
% 2.77/3.04  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('111', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.77/3.04         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.77/3.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.77/3.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.77/3.04          | ~ (v1_funct_1 @ X1))),
% 2.77/3.04      inference('demod', [status(thm)], ['109', '110'])).
% 2.77/3.04  thf('112', plain,
% 2.77/3.04      ((~ (v1_funct_1 @ sk_D)
% 2.77/3.04        | (m1_subset_1 @ 
% 2.77/3.04           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.77/3.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.77/3.04      inference('sup-', [status(thm)], ['106', '111'])).
% 2.77/3.04  thf('113', plain, ((v1_funct_1 @ sk_D)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('114', plain,
% 2.77/3.04      ((m1_subset_1 @ 
% 2.77/3.04        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.77/3.04        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.77/3.04      inference('demod', [status(thm)], ['112', '113'])).
% 2.77/3.04  thf(redefinition_r2_relset_1, axiom,
% 2.77/3.04    (![A:$i,B:$i,C:$i,D:$i]:
% 2.77/3.04     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.77/3.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/3.04       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.77/3.04  thf('115', plain,
% 2.77/3.04      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.77/3.04         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 2.77/3.04          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 2.77/3.04          | ((X19) = (X22))
% 2.77/3.04          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 2.77/3.04      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.77/3.04  thf('116', plain,
% 2.77/3.04      (![X0 : $i]:
% 2.77/3.04         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/3.04             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.77/3.04          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.77/3.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.77/3.04      inference('sup-', [status(thm)], ['114', '115'])).
% 2.77/3.04  thf('117', plain,
% 2.77/3.04      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.77/3.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.77/3.04        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.77/3.04            = (k6_partfun1 @ sk_A)))),
% 2.77/3.04      inference('sup-', [status(thm)], ['105', '116'])).
% 2.77/3.04  thf('118', plain,
% 2.77/3.04      (![X23 : $i]:
% 2.77/3.04         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 2.77/3.04          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 2.77/3.04      inference('demod', [status(thm)], ['8', '9'])).
% 2.77/3.04  thf('119', plain,
% 2.77/3.04      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.77/3.04         = (k6_partfun1 @ sk_A))),
% 2.77/3.04      inference('demod', [status(thm)], ['117', '118'])).
% 2.77/3.04  thf('120', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf(t26_funct_2, axiom,
% 2.77/3.04    (![A:$i,B:$i,C:$i,D:$i]:
% 2.77/3.04     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.77/3.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/3.04       ( ![E:$i]:
% 2.77/3.04         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.77/3.04             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.77/3.04           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.77/3.04             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.77/3.04               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.77/3.04  thf('121', plain,
% 2.77/3.04      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.77/3.04         (~ (v1_funct_1 @ X37)
% 2.77/3.04          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.77/3.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.77/3.04          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 2.77/3.04          | (v2_funct_1 @ X41)
% 2.77/3.04          | ((X39) = (k1_xboole_0))
% 2.77/3.04          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 2.77/3.04          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 2.77/3.04          | ~ (v1_funct_1 @ X41))),
% 2.77/3.04      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.77/3.04  thf('122', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (~ (v1_funct_1 @ X0)
% 2.77/3.04          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.77/3.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.77/3.04          | ((sk_A) = (k1_xboole_0))
% 2.77/3.04          | (v2_funct_1 @ X0)
% 2.77/3.04          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.77/3.04          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.77/3.04          | ~ (v1_funct_1 @ sk_D))),
% 2.77/3.04      inference('sup-', [status(thm)], ['120', '121'])).
% 2.77/3.04  thf('123', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('125', plain,
% 2.77/3.04      (![X0 : $i, X1 : $i]:
% 2.77/3.04         (~ (v1_funct_1 @ X0)
% 2.77/3.04          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.77/3.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.77/3.04          | ((sk_A) = (k1_xboole_0))
% 2.77/3.04          | (v2_funct_1 @ X0)
% 2.77/3.04          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.77/3.04      inference('demod', [status(thm)], ['122', '123', '124'])).
% 2.77/3.04  thf('126', plain,
% 2.77/3.04      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.77/3.04        | (v2_funct_1 @ sk_C)
% 2.77/3.04        | ((sk_A) = (k1_xboole_0))
% 2.77/3.04        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.77/3.04        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.77/3.04        | ~ (v1_funct_1 @ sk_C))),
% 2.77/3.04      inference('sup-', [status(thm)], ['119', '125'])).
% 2.77/3.04  thf('127', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 2.77/3.04      inference('demod', [status(thm)], ['52', '53'])).
% 2.77/3.04  thf('128', plain,
% 2.77/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('129', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 2.77/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/3.04  thf('131', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.77/3.04      inference('demod', [status(thm)], ['126', '127', '128', '129', '130'])).
% 2.77/3.04  thf('132', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/3.04      inference('split', [status(esa)], ['57'])).
% 2.77/3.04  thf('133', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.77/3.04      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 2.77/3.04  thf('134', plain, (~ (v2_funct_1 @ sk_C)),
% 2.77/3.04      inference('simpl_trail', [status(thm)], ['132', '133'])).
% 2.77/3.04  thf('135', plain, (((sk_A) = (k1_xboole_0))),
% 2.77/3.04      inference('clc', [status(thm)], ['131', '134'])).
% 2.77/3.04  thf('136', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.77/3.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.77/3.04  thf('137', plain, ($false),
% 2.77/3.04      inference('demod', [status(thm)], ['104', '135', '136'])).
% 2.77/3.04  
% 2.77/3.04  % SZS output end Refutation
% 2.77/3.04  
% 2.77/3.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
