%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zl6FS9R60M

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:09 EST 2020

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 531 expanded)
%              Number of leaves         :   39 ( 175 expanded)
%              Depth                    :   19
%              Number of atoms          : 1416 (7938 expanded)
%              Number of equality atoms :   60 ( 222 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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

thf('6',plain,(
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

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('13',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','26'])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','26'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != X23 )
      | ( v2_funct_2 @ X24 @ X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('41',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','46'])).

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
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('52',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('53',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37 ) @ ( k6_partfun1 @ X35 ) )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('63',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37 ) @ ( k6_relat_1 @ X35 ) )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    inference(demod,[status(thm)],['69','72','73','74','75'])).

thf('77',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('78',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['69','72','73','74','75'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['78','81','82','85'])).

thf('87',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('88',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('90',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['57','90'])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('96',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['92','101'])).

thf('103',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
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

thf('106',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('113',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('117',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
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

thf('119',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X41 @ X39 @ X39 @ X40 @ X42 @ X38 ) )
      | ( v2_funct_1 @ X42 )
      | ( X40 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X39 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['55'])).

thf('131',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('132',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['130','131'])).

thf('133',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['129','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['102','133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zl6FS9R60M
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.19/3.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.19/3.37  % Solved by: fo/fo7.sh
% 3.19/3.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.19/3.37  % done 3543 iterations in 2.918s
% 3.19/3.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.19/3.37  % SZS output start Refutation
% 3.19/3.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.19/3.37  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.19/3.37  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.19/3.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.19/3.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.19/3.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.19/3.37  thf(sk_B_type, type, sk_B: $i).
% 3.19/3.37  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.19/3.37  thf(sk_D_type, type, sk_D: $i).
% 3.19/3.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.19/3.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.19/3.37  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.19/3.37  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.19/3.37  thf(sk_A_type, type, sk_A: $i).
% 3.19/3.37  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.19/3.37  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.19/3.37  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.19/3.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.19/3.37  thf(sk_C_type, type, sk_C: $i).
% 3.19/3.37  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.19/3.37  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.19/3.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.19/3.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.19/3.37  thf(t29_funct_2, conjecture,
% 3.19/3.37    (![A:$i,B:$i,C:$i]:
% 3.19/3.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.19/3.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.37       ( ![D:$i]:
% 3.19/3.37         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.19/3.37             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.19/3.37           ( ( r2_relset_1 @
% 3.19/3.37               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.19/3.37               ( k6_partfun1 @ A ) ) =>
% 3.19/3.37             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.19/3.37  thf(zf_stmt_0, negated_conjecture,
% 3.19/3.37    (~( ![A:$i,B:$i,C:$i]:
% 3.19/3.37        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.19/3.37            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.37          ( ![D:$i]:
% 3.19/3.37            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.19/3.37                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.19/3.37              ( ( r2_relset_1 @
% 3.19/3.37                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.19/3.37                  ( k6_partfun1 @ A ) ) =>
% 3.19/3.37                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.19/3.37    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.19/3.37  thf('0', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf(redefinition_k2_relset_1, axiom,
% 3.19/3.37    (![A:$i,B:$i,C:$i]:
% 3.19/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.37       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.19/3.37  thf('1', plain,
% 3.19/3.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.19/3.37         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 3.19/3.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.19/3.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.19/3.37  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.19/3.37      inference('sup-', [status(thm)], ['0', '1'])).
% 3.19/3.37  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.19/3.37  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.19/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.19/3.37  thf(t8_boole, axiom,
% 3.19/3.37    (![A:$i,B:$i]:
% 3.19/3.37     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.19/3.37  thf('4', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.19/3.37      inference('cnf', [status(esa)], [t8_boole])).
% 3.19/3.37  thf('5', plain,
% 3.19/3.37      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.37  thf('6', plain,
% 3.19/3.37      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.37  thf(t113_zfmisc_1, axiom,
% 3.19/3.37    (![A:$i,B:$i]:
% 3.19/3.37     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.19/3.37       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.19/3.37  thf('7', plain,
% 3.19/3.37      (![X3 : $i, X4 : $i]:
% 3.19/3.37         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.19/3.37      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.19/3.37  thf('8', plain,
% 3.19/3.37      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.19/3.37      inference('simplify', [status(thm)], ['7'])).
% 3.19/3.37  thf('9', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup+', [status(thm)], ['6', '8'])).
% 3.19/3.37  thf('10', plain,
% 3.19/3.37      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.37  thf('11', plain,
% 3.19/3.37      (![X3 : $i, X4 : $i]:
% 3.19/3.37         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 3.19/3.37      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.19/3.37  thf('12', plain,
% 3.19/3.37      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.37      inference('simplify', [status(thm)], ['11'])).
% 3.19/3.37  thf(dt_k6_partfun1, axiom,
% 3.19/3.37    (![A:$i]:
% 3.19/3.37     ( ( m1_subset_1 @
% 3.19/3.37         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.19/3.37       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.19/3.37  thf('13', plain,
% 3.19/3.37      (![X32 : $i]:
% 3.19/3.37         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 3.19/3.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 3.19/3.37      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.19/3.37  thf(redefinition_k6_partfun1, axiom,
% 3.19/3.37    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.19/3.37  thf('14', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 3.19/3.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.19/3.37  thf('15', plain,
% 3.19/3.37      (![X32 : $i]:
% 3.19/3.37         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 3.19/3.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 3.19/3.37      inference('demod', [status(thm)], ['13', '14'])).
% 3.19/3.37  thf('16', plain,
% 3.19/3.37      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.19/3.37      inference('sup+', [status(thm)], ['12', '15'])).
% 3.19/3.37  thf('17', plain,
% 3.19/3.37      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.19/3.37      inference('sup+', [status(thm)], ['12', '15'])).
% 3.19/3.37  thf('18', plain,
% 3.19/3.37      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.37      inference('simplify', [status(thm)], ['11'])).
% 3.19/3.37  thf(cc4_relset_1, axiom,
% 3.19/3.37    (![A:$i,B:$i]:
% 3.19/3.37     ( ( v1_xboole_0 @ A ) =>
% 3.19/3.37       ( ![C:$i]:
% 3.19/3.37         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 3.19/3.37           ( v1_xboole_0 @ C ) ) ) ))).
% 3.19/3.37  thf('19', plain,
% 3.19/3.37      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.19/3.37         (~ (v1_xboole_0 @ X13)
% 3.19/3.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 3.19/3.37          | (v1_xboole_0 @ X14))),
% 3.19/3.37      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.19/3.37  thf('20', plain,
% 3.19/3.37      (![X1 : $i]:
% 3.19/3.37         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.19/3.37          | (v1_xboole_0 @ X1)
% 3.19/3.37          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['18', '19'])).
% 3.19/3.37  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.19/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.19/3.37  thf('22', plain,
% 3.19/3.37      (![X1 : $i]:
% 3.19/3.37         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.19/3.37          | (v1_xboole_0 @ X1))),
% 3.19/3.37      inference('demod', [status(thm)], ['20', '21'])).
% 3.19/3.37  thf('23', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['17', '22'])).
% 3.19/3.37  thf('24', plain,
% 3.19/3.37      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.37  thf('25', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['23', '24'])).
% 3.19/3.37  thf('26', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.19/3.37      inference('demod', [status(thm)], ['16', '25'])).
% 3.19/3.37  thf('27', plain,
% 3.19/3.37      (![X0 : $i]:
% 3.19/3.37         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.19/3.37          | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup+', [status(thm)], ['10', '26'])).
% 3.19/3.37  thf('28', plain,
% 3.19/3.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.19/3.37         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 3.19/3.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.19/3.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.19/3.37  thf('29', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.19/3.37          | ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 3.19/3.37      inference('sup-', [status(thm)], ['27', '28'])).
% 3.19/3.37  thf('30', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.19/3.37          | ~ (v1_xboole_0 @ X1)
% 3.19/3.37          | ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 3.19/3.37      inference('sup-', [status(thm)], ['9', '29'])).
% 3.19/3.37  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.19/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.19/3.37  thf('32', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (v1_xboole_0 @ X1)
% 3.19/3.37          | ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 3.19/3.37      inference('demod', [status(thm)], ['30', '31'])).
% 3.19/3.37  thf('33', plain,
% 3.19/3.37      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.19/3.37      inference('simplify', [status(thm)], ['7'])).
% 3.19/3.37  thf('34', plain,
% 3.19/3.37      (![X0 : $i]:
% 3.19/3.37         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.19/3.37          | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup+', [status(thm)], ['10', '26'])).
% 3.19/3.37  thf(cc2_relset_1, axiom,
% 3.19/3.37    (![A:$i,B:$i,C:$i]:
% 3.19/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.37       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.19/3.37  thf('35', plain,
% 3.19/3.37      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.37         ((v5_relat_1 @ X10 @ X12)
% 3.19/3.37          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.19/3.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.19/3.37  thf('36', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.19/3.37          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['34', '35'])).
% 3.19/3.37  thf('37', plain,
% 3.19/3.37      (![X0 : $i]:
% 3.19/3.37         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['33', '36'])).
% 3.19/3.37  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.19/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.19/3.37  thf('39', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 3.19/3.37      inference('demod', [status(thm)], ['37', '38'])).
% 3.19/3.37  thf(d3_funct_2, axiom,
% 3.19/3.37    (![A:$i,B:$i]:
% 3.19/3.37     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.19/3.37       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.19/3.37  thf('40', plain,
% 3.19/3.37      (![X23 : $i, X24 : $i]:
% 3.19/3.37         (((k2_relat_1 @ X24) != (X23))
% 3.19/3.37          | (v2_funct_2 @ X24 @ X23)
% 3.19/3.37          | ~ (v5_relat_1 @ X24 @ X23)
% 3.19/3.37          | ~ (v1_relat_1 @ X24))),
% 3.19/3.37      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.19/3.37  thf('41', plain,
% 3.19/3.37      (![X24 : $i]:
% 3.19/3.37         (~ (v1_relat_1 @ X24)
% 3.19/3.37          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 3.19/3.37          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 3.19/3.37      inference('simplify', [status(thm)], ['40'])).
% 3.19/3.37  thf('42', plain,
% 3.19/3.37      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 3.19/3.37        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['39', '41'])).
% 3.19/3.37  thf('43', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['23', '24'])).
% 3.19/3.37  thf(fc4_funct_1, axiom,
% 3.19/3.37    (![A:$i]:
% 3.19/3.37     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.19/3.37       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.19/3.37  thf('44', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 3.19/3.37      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.19/3.37  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.19/3.37      inference('sup+', [status(thm)], ['43', '44'])).
% 3.19/3.37  thf('46', plain, ((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 3.19/3.37      inference('demod', [status(thm)], ['42', '45'])).
% 3.19/3.37  thf('47', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 3.19/3.37          | ~ (v1_xboole_0 @ X1))),
% 3.19/3.37      inference('sup+', [status(thm)], ['32', '46'])).
% 3.19/3.37  thf('48', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.37         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X2 @ X1 @ X0))
% 3.19/3.37          | ~ (v1_xboole_0 @ X0)
% 3.19/3.37          | ~ (v1_xboole_0 @ X2))),
% 3.19/3.37      inference('sup+', [status(thm)], ['5', '47'])).
% 3.19/3.37  thf('49', plain,
% 3.19/3.37      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.19/3.37        | ~ (v1_xboole_0 @ sk_A)
% 3.19/3.37        | ~ (v1_xboole_0 @ sk_C))),
% 3.19/3.37      inference('sup+', [status(thm)], ['2', '48'])).
% 3.19/3.37  thf('50', plain,
% 3.19/3.37      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.37  thf('51', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['23', '24'])).
% 3.19/3.37  thf('52', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 3.19/3.37      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.19/3.37  thf('53', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.19/3.37      inference('sup+', [status(thm)], ['51', '52'])).
% 3.19/3.37  thf('54', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup+', [status(thm)], ['50', '53'])).
% 3.19/3.37  thf('55', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('56', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.19/3.37      inference('split', [status(esa)], ['55'])).
% 3.19/3.37  thf('57', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.19/3.37      inference('sup-', [status(thm)], ['54', '56'])).
% 3.19/3.37  thf('58', plain,
% 3.19/3.37      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.37        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.19/3.37        (k6_partfun1 @ sk_A))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('59', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 3.19/3.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.19/3.37  thf('60', plain,
% 3.19/3.37      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.37        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.19/3.37        (k6_relat_1 @ sk_A))),
% 3.19/3.37      inference('demod', [status(thm)], ['58', '59'])).
% 3.19/3.37  thf('61', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf(t24_funct_2, axiom,
% 3.19/3.37    (![A:$i,B:$i,C:$i]:
% 3.19/3.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.19/3.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.37       ( ![D:$i]:
% 3.19/3.37         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.19/3.37             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.19/3.37           ( ( r2_relset_1 @
% 3.19/3.37               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.19/3.37               ( k6_partfun1 @ B ) ) =>
% 3.19/3.37             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.19/3.37  thf('62', plain,
% 3.19/3.37      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.19/3.37         (~ (v1_funct_1 @ X34)
% 3.19/3.37          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 3.19/3.37          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.19/3.37          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 3.19/3.37               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 3.19/3.37               (k6_partfun1 @ X35))
% 3.19/3.37          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 3.19/3.37          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 3.19/3.37          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 3.19/3.37          | ~ (v1_funct_1 @ X37))),
% 3.19/3.37      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.19/3.37  thf('63', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 3.19/3.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.19/3.37  thf('64', plain,
% 3.19/3.37      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.19/3.37         (~ (v1_funct_1 @ X34)
% 3.19/3.37          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 3.19/3.37          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.19/3.37          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 3.19/3.37               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 3.19/3.37               (k6_relat_1 @ X35))
% 3.19/3.37          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 3.19/3.37          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 3.19/3.37          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 3.19/3.37          | ~ (v1_funct_1 @ X37))),
% 3.19/3.37      inference('demod', [status(thm)], ['62', '63'])).
% 3.19/3.37  thf('65', plain,
% 3.19/3.37      (![X0 : $i]:
% 3.19/3.37         (~ (v1_funct_1 @ X0)
% 3.19/3.37          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.19/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.19/3.37          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.19/3.37          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.37               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.19/3.37               (k6_relat_1 @ sk_A))
% 3.19/3.37          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.19/3.37          | ~ (v1_funct_1 @ sk_C))),
% 3.19/3.37      inference('sup-', [status(thm)], ['61', '64'])).
% 3.19/3.37  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('68', plain,
% 3.19/3.37      (![X0 : $i]:
% 3.19/3.37         (~ (v1_funct_1 @ X0)
% 3.19/3.37          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.19/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.19/3.37          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.19/3.37          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.37               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.19/3.37               (k6_relat_1 @ sk_A)))),
% 3.19/3.37      inference('demod', [status(thm)], ['65', '66', '67'])).
% 3.19/3.37  thf('69', plain,
% 3.19/3.37      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.19/3.37        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.19/3.37        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.19/3.37        | ~ (v1_funct_1 @ sk_D))),
% 3.19/3.37      inference('sup-', [status(thm)], ['60', '68'])).
% 3.19/3.37  thf('70', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('71', plain,
% 3.19/3.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.19/3.37         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 3.19/3.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.19/3.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.19/3.37  thf('72', plain,
% 3.19/3.37      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.19/3.37      inference('sup-', [status(thm)], ['70', '71'])).
% 3.19/3.37  thf('73', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('76', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.19/3.37      inference('demod', [status(thm)], ['69', '72', '73', '74', '75'])).
% 3.19/3.37  thf('77', plain,
% 3.19/3.37      (![X24 : $i]:
% 3.19/3.37         (~ (v1_relat_1 @ X24)
% 3.19/3.37          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 3.19/3.37          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 3.19/3.37      inference('simplify', [status(thm)], ['40'])).
% 3.19/3.37  thf('78', plain,
% 3.19/3.37      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.19/3.37        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.19/3.37        | ~ (v1_relat_1 @ sk_D))),
% 3.19/3.37      inference('sup-', [status(thm)], ['76', '77'])).
% 3.19/3.37  thf('79', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('80', plain,
% 3.19/3.37      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.37         ((v5_relat_1 @ X10 @ X12)
% 3.19/3.37          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.19/3.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.19/3.37  thf('81', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.19/3.37      inference('sup-', [status(thm)], ['79', '80'])).
% 3.19/3.37  thf('82', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.19/3.37      inference('demod', [status(thm)], ['69', '72', '73', '74', '75'])).
% 3.19/3.37  thf('83', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf(cc1_relset_1, axiom,
% 3.19/3.37    (![A:$i,B:$i,C:$i]:
% 3.19/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.19/3.37       ( v1_relat_1 @ C ) ))).
% 3.19/3.37  thf('84', plain,
% 3.19/3.37      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.19/3.37         ((v1_relat_1 @ X7)
% 3.19/3.37          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.19/3.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.19/3.37  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 3.19/3.37      inference('sup-', [status(thm)], ['83', '84'])).
% 3.19/3.37  thf('86', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.19/3.37      inference('demod', [status(thm)], ['78', '81', '82', '85'])).
% 3.19/3.37  thf('87', plain,
% 3.19/3.37      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.19/3.37      inference('split', [status(esa)], ['55'])).
% 3.19/3.37  thf('88', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.19/3.37      inference('sup-', [status(thm)], ['86', '87'])).
% 3.19/3.37  thf('89', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.19/3.37      inference('split', [status(esa)], ['55'])).
% 3.19/3.37  thf('90', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.19/3.37      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 3.19/3.37  thf('91', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.19/3.37      inference('simpl_trail', [status(thm)], ['57', '90'])).
% 3.19/3.37  thf('92', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.19/3.37      inference('clc', [status(thm)], ['49', '91'])).
% 3.19/3.37  thf('93', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup+', [status(thm)], ['6', '8'])).
% 3.19/3.37  thf('94', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('95', plain,
% 3.19/3.37      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.19/3.37      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.37  thf('96', plain,
% 3.19/3.37      (![X1 : $i]:
% 3.19/3.37         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.19/3.37          | (v1_xboole_0 @ X1))),
% 3.19/3.37      inference('demod', [status(thm)], ['20', '21'])).
% 3.19/3.37  thf('97', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 3.19/3.37          | ~ (v1_xboole_0 @ X0)
% 3.19/3.37          | (v1_xboole_0 @ X1))),
% 3.19/3.37      inference('sup-', [status(thm)], ['95', '96'])).
% 3.19/3.37  thf('98', plain,
% 3.19/3.37      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.19/3.37      inference('sup-', [status(thm)], ['94', '97'])).
% 3.19/3.37  thf('99', plain,
% 3.19/3.37      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.19/3.37        | ~ (v1_xboole_0 @ sk_A)
% 3.19/3.37        | (v1_xboole_0 @ sk_C))),
% 3.19/3.37      inference('sup-', [status(thm)], ['93', '98'])).
% 3.19/3.37  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.19/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.19/3.37  thf('101', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.19/3.37      inference('demod', [status(thm)], ['99', '100'])).
% 3.19/3.37  thf('102', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.19/3.37      inference('clc', [status(thm)], ['92', '101'])).
% 3.19/3.37  thf('103', plain,
% 3.19/3.37      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.37        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.19/3.37        (k6_relat_1 @ sk_A))),
% 3.19/3.37      inference('demod', [status(thm)], ['58', '59'])).
% 3.19/3.37  thf('104', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('105', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf(dt_k1_partfun1, axiom,
% 3.19/3.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.19/3.37     ( ( ( v1_funct_1 @ E ) & 
% 3.19/3.37         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.19/3.37         ( v1_funct_1 @ F ) & 
% 3.19/3.37         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.19/3.37       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.19/3.37         ( m1_subset_1 @
% 3.19/3.37           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.19/3.37           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.19/3.37  thf('106', plain,
% 3.19/3.37      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.19/3.37         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.19/3.37          | ~ (v1_funct_1 @ X25)
% 3.19/3.37          | ~ (v1_funct_1 @ X28)
% 3.19/3.37          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.19/3.37          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 3.19/3.37             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 3.19/3.37      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.19/3.37  thf('107', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.37         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.19/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.19/3.37          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.19/3.37          | ~ (v1_funct_1 @ X1)
% 3.19/3.37          | ~ (v1_funct_1 @ sk_C))),
% 3.19/3.37      inference('sup-', [status(thm)], ['105', '106'])).
% 3.19/3.37  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('109', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.37         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.19/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.19/3.37          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.19/3.37          | ~ (v1_funct_1 @ X1))),
% 3.19/3.37      inference('demod', [status(thm)], ['107', '108'])).
% 3.19/3.37  thf('110', plain,
% 3.19/3.37      ((~ (v1_funct_1 @ sk_D)
% 3.19/3.37        | (m1_subset_1 @ 
% 3.19/3.37           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.19/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.19/3.37      inference('sup-', [status(thm)], ['104', '109'])).
% 3.19/3.37  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('112', plain,
% 3.19/3.37      ((m1_subset_1 @ 
% 3.19/3.37        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.19/3.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.19/3.37      inference('demod', [status(thm)], ['110', '111'])).
% 3.19/3.37  thf(redefinition_r2_relset_1, axiom,
% 3.19/3.37    (![A:$i,B:$i,C:$i,D:$i]:
% 3.19/3.37     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.19/3.37         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.37       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.19/3.37  thf('113', plain,
% 3.19/3.37      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.19/3.37         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.19/3.37          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.19/3.37          | ((X19) = (X22))
% 3.19/3.37          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 3.19/3.37      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.19/3.37  thf('114', plain,
% 3.19/3.37      (![X0 : $i]:
% 3.19/3.37         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.19/3.37             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.19/3.37          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.19/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.19/3.37      inference('sup-', [status(thm)], ['112', '113'])).
% 3.19/3.37  thf('115', plain,
% 3.19/3.37      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.19/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.19/3.37        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.19/3.37            = (k6_relat_1 @ sk_A)))),
% 3.19/3.37      inference('sup-', [status(thm)], ['103', '114'])).
% 3.19/3.37  thf('116', plain,
% 3.19/3.37      (![X32 : $i]:
% 3.19/3.37         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 3.19/3.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 3.19/3.37      inference('demod', [status(thm)], ['13', '14'])).
% 3.19/3.37  thf('117', plain,
% 3.19/3.37      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.19/3.37         = (k6_relat_1 @ sk_A))),
% 3.19/3.37      inference('demod', [status(thm)], ['115', '116'])).
% 3.19/3.37  thf('118', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf(t26_funct_2, axiom,
% 3.19/3.37    (![A:$i,B:$i,C:$i,D:$i]:
% 3.19/3.37     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.19/3.37         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.19/3.37       ( ![E:$i]:
% 3.19/3.37         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.19/3.37             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.19/3.37           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.19/3.37             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.19/3.37               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.19/3.37  thf('119', plain,
% 3.19/3.37      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.19/3.37         (~ (v1_funct_1 @ X38)
% 3.19/3.37          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 3.19/3.37          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 3.19/3.37          | ~ (v2_funct_1 @ (k1_partfun1 @ X41 @ X39 @ X39 @ X40 @ X42 @ X38))
% 3.19/3.37          | (v2_funct_1 @ X42)
% 3.19/3.37          | ((X40) = (k1_xboole_0))
% 3.19/3.37          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 3.19/3.37          | ~ (v1_funct_2 @ X42 @ X41 @ X39)
% 3.19/3.37          | ~ (v1_funct_1 @ X42))),
% 3.19/3.37      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.19/3.37  thf('120', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (v1_funct_1 @ X0)
% 3.19/3.37          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.19/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.19/3.37          | ((sk_A) = (k1_xboole_0))
% 3.19/3.37          | (v2_funct_1 @ X0)
% 3.19/3.37          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.19/3.37          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.19/3.37          | ~ (v1_funct_1 @ sk_D))),
% 3.19/3.37      inference('sup-', [status(thm)], ['118', '119'])).
% 3.19/3.37  thf('121', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('122', plain, ((v1_funct_1 @ sk_D)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('123', plain,
% 3.19/3.37      (![X0 : $i, X1 : $i]:
% 3.19/3.37         (~ (v1_funct_1 @ X0)
% 3.19/3.37          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.19/3.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.19/3.37          | ((sk_A) = (k1_xboole_0))
% 3.19/3.37          | (v2_funct_1 @ X0)
% 3.19/3.37          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.19/3.37      inference('demod', [status(thm)], ['120', '121', '122'])).
% 3.19/3.37  thf('124', plain,
% 3.19/3.37      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.19/3.37        | (v2_funct_1 @ sk_C)
% 3.19/3.37        | ((sk_A) = (k1_xboole_0))
% 3.19/3.37        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.19/3.37        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.19/3.37        | ~ (v1_funct_1 @ sk_C))),
% 3.19/3.37      inference('sup-', [status(thm)], ['117', '123'])).
% 3.19/3.37  thf('125', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 3.19/3.37      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.19/3.37  thf('126', plain,
% 3.19/3.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('127', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 3.19/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.37  thf('129', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.19/3.37      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 3.19/3.37  thf('130', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.19/3.37      inference('split', [status(esa)], ['55'])).
% 3.19/3.37  thf('131', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.19/3.37      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 3.19/3.37  thf('132', plain, (~ (v2_funct_1 @ sk_C)),
% 3.19/3.37      inference('simpl_trail', [status(thm)], ['130', '131'])).
% 3.19/3.37  thf('133', plain, (((sk_A) = (k1_xboole_0))),
% 3.19/3.37      inference('clc', [status(thm)], ['129', '132'])).
% 3.19/3.37  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.19/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.19/3.37  thf('135', plain, ($false),
% 3.19/3.37      inference('demod', [status(thm)], ['102', '133', '134'])).
% 3.19/3.37  
% 3.19/3.37  % SZS output end Refutation
% 3.19/3.37  
% 3.19/3.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
