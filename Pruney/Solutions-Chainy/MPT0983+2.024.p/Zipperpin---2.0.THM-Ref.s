%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zgpKjltoQP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:04 EST 2020

% Result     : Theorem 3.45s
% Output     : Refutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 466 expanded)
%              Number of leaves         :   39 ( 155 expanded)
%              Depth                    :   20
%              Number of atoms          : 1378 (7564 expanded)
%              Number of equality atoms :   57 ( 176 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('17',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','19'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('37',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','43'])).

thf('45',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('48',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('49',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('59',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_relat_1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['65','68','69','70','71'])).

thf('73',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('74',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['65','68','69','70','71'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['74','77','78','81'])).

thf('83',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('84',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('86',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['53','86'])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['88','95'])).

thf('97',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('107',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('111',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
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

thf('113',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36 ) )
      | ( v2_funct_1 @ X40 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['51'])).

thf('125',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('126',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['124','125'])).

thf('127',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['123','126'])).

thf('128',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['96','127','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zgpKjltoQP
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.45/3.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.45/3.66  % Solved by: fo/fo7.sh
% 3.45/3.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.45/3.66  % done 3810 iterations in 3.215s
% 3.45/3.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.45/3.66  % SZS output start Refutation
% 3.45/3.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.45/3.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.45/3.66  thf(sk_B_type, type, sk_B: $i).
% 3.45/3.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.45/3.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.45/3.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.45/3.66  thf(sk_A_type, type, sk_A: $i).
% 3.45/3.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.45/3.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.45/3.66  thf(sk_C_type, type, sk_C: $i).
% 3.45/3.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.45/3.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.45/3.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.45/3.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.45/3.66  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.45/3.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.45/3.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.45/3.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.45/3.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.45/3.66  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.45/3.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.45/3.66  thf(sk_D_type, type, sk_D: $i).
% 3.45/3.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.45/3.66  thf(t29_funct_2, conjecture,
% 3.45/3.66    (![A:$i,B:$i,C:$i]:
% 3.45/3.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.45/3.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.66       ( ![D:$i]:
% 3.45/3.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.45/3.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.45/3.66           ( ( r2_relset_1 @
% 3.45/3.66               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.45/3.66               ( k6_partfun1 @ A ) ) =>
% 3.45/3.66             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.45/3.66  thf(zf_stmt_0, negated_conjecture,
% 3.45/3.66    (~( ![A:$i,B:$i,C:$i]:
% 3.45/3.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.45/3.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.66          ( ![D:$i]:
% 3.45/3.66            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.45/3.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.45/3.66              ( ( r2_relset_1 @
% 3.45/3.66                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.45/3.66                  ( k6_partfun1 @ A ) ) =>
% 3.45/3.66                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.45/3.66    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.45/3.66  thf('0', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf(redefinition_k2_relset_1, axiom,
% 3.45/3.66    (![A:$i,B:$i,C:$i]:
% 3.45/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.45/3.66  thf('1', plain,
% 3.45/3.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.66         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.45/3.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.45/3.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.45/3.66  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.45/3.66      inference('sup-', [status(thm)], ['0', '1'])).
% 3.45/3.66  thf(l13_xboole_0, axiom,
% 3.45/3.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.45/3.66  thf('3', plain,
% 3.45/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.45/3.66  thf(t113_zfmisc_1, axiom,
% 3.45/3.66    (![A:$i,B:$i]:
% 3.45/3.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.45/3.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.45/3.66  thf('4', plain,
% 3.45/3.66      (![X2 : $i, X3 : $i]:
% 3.45/3.66         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.45/3.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.45/3.66  thf('5', plain,
% 3.45/3.66      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 3.45/3.66      inference('simplify', [status(thm)], ['4'])).
% 3.45/3.66  thf(dt_k6_partfun1, axiom,
% 3.45/3.66    (![A:$i]:
% 3.45/3.66     ( ( m1_subset_1 @
% 3.45/3.66         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.45/3.66       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.45/3.66  thf('6', plain,
% 3.45/3.66      (![X30 : $i]:
% 3.45/3.66         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 3.45/3.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 3.45/3.66      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.45/3.66  thf(redefinition_k6_partfun1, axiom,
% 3.45/3.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.45/3.66  thf('7', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.45/3.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.45/3.66  thf('8', plain,
% 3.45/3.66      (![X30 : $i]:
% 3.45/3.66         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 3.45/3.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 3.45/3.66      inference('demod', [status(thm)], ['6', '7'])).
% 3.45/3.66  thf(cc1_subset_1, axiom,
% 3.45/3.66    (![A:$i]:
% 3.45/3.66     ( ( v1_xboole_0 @ A ) =>
% 3.45/3.66       ( ![B:$i]:
% 3.45/3.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.45/3.66  thf('9', plain,
% 3.45/3.66      (![X4 : $i, X5 : $i]:
% 3.45/3.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.45/3.66          | (v1_xboole_0 @ X4)
% 3.45/3.66          | ~ (v1_xboole_0 @ X5))),
% 3.45/3.66      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.45/3.66  thf('10', plain,
% 3.45/3.66      (![X0 : $i]:
% 3.45/3.66         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 3.45/3.66          | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 3.45/3.66      inference('sup-', [status(thm)], ['8', '9'])).
% 3.45/3.66  thf('11', plain,
% 3.45/3.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.45/3.66        | (v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0)))),
% 3.45/3.66      inference('sup-', [status(thm)], ['5', '10'])).
% 3.45/3.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.45/3.66  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.45/3.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.45/3.66  thf('13', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.45/3.66      inference('demod', [status(thm)], ['11', '12'])).
% 3.45/3.66  thf('14', plain,
% 3.45/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.45/3.66  thf('15', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.45/3.66      inference('sup-', [status(thm)], ['13', '14'])).
% 3.45/3.66  thf('16', plain,
% 3.45/3.66      (![X30 : $i]:
% 3.45/3.66         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 3.45/3.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 3.45/3.66      inference('demod', [status(thm)], ['6', '7'])).
% 3.45/3.66  thf('17', plain,
% 3.45/3.66      ((m1_subset_1 @ k1_xboole_0 @ 
% 3.45/3.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.45/3.66      inference('sup+', [status(thm)], ['15', '16'])).
% 3.45/3.66  thf('18', plain,
% 3.45/3.66      (![X2 : $i, X3 : $i]:
% 3.45/3.66         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 3.45/3.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.45/3.66  thf('19', plain,
% 3.45/3.66      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.45/3.66      inference('simplify', [status(thm)], ['18'])).
% 3.45/3.66  thf('20', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.45/3.66      inference('demod', [status(thm)], ['17', '19'])).
% 3.45/3.66  thf('21', plain,
% 3.45/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.45/3.66  thf('22', plain,
% 3.45/3.66      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.45/3.66      inference('simplify', [status(thm)], ['18'])).
% 3.45/3.66  thf('23', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i]:
% 3.45/3.66         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('sup+', [status(thm)], ['21', '22'])).
% 3.45/3.66  thf('24', plain,
% 3.45/3.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.66         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.45/3.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.45/3.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.45/3.66  thf('25', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.66         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.45/3.66          | ~ (v1_xboole_0 @ X1)
% 3.45/3.66          | ((k2_relset_1 @ X1 @ X0 @ X2) = (k2_relat_1 @ X2)))),
% 3.45/3.66      inference('sup-', [status(thm)], ['23', '24'])).
% 3.45/3.66  thf('26', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i]:
% 3.45/3.66         (((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 3.45/3.66          | ~ (v1_xboole_0 @ X1))),
% 3.45/3.66      inference('sup-', [status(thm)], ['20', '25'])).
% 3.45/3.66  thf('27', plain,
% 3.45/3.66      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.45/3.66      inference('simplify', [status(thm)], ['18'])).
% 3.45/3.66  thf('28', plain,
% 3.45/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.45/3.66  thf('29', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.45/3.66      inference('demod', [status(thm)], ['17', '19'])).
% 3.45/3.66  thf('30', plain,
% 3.45/3.66      (![X0 : $i]:
% 3.45/3.66         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.45/3.66          | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('sup+', [status(thm)], ['28', '29'])).
% 3.45/3.66  thf(cc2_relset_1, axiom,
% 3.45/3.66    (![A:$i,B:$i,C:$i]:
% 3.45/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.45/3.66  thf('31', plain,
% 3.45/3.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.45/3.66         ((v5_relat_1 @ X11 @ X13)
% 3.45/3.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.45/3.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.45/3.66  thf('32', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i]:
% 3.45/3.66         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.45/3.66          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.45/3.66      inference('sup-', [status(thm)], ['30', '31'])).
% 3.45/3.66  thf('33', plain,
% 3.45/3.66      (![X0 : $i]:
% 3.45/3.66         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.45/3.66      inference('sup-', [status(thm)], ['27', '32'])).
% 3.45/3.66  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.45/3.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.45/3.66  thf('35', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 3.45/3.66      inference('demod', [status(thm)], ['33', '34'])).
% 3.45/3.66  thf(d3_funct_2, axiom,
% 3.45/3.66    (![A:$i,B:$i]:
% 3.45/3.66     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.45/3.66       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.45/3.66  thf('36', plain,
% 3.45/3.66      (![X21 : $i, X22 : $i]:
% 3.45/3.66         (((k2_relat_1 @ X22) != (X21))
% 3.45/3.66          | (v2_funct_2 @ X22 @ X21)
% 3.45/3.66          | ~ (v5_relat_1 @ X22 @ X21)
% 3.45/3.66          | ~ (v1_relat_1 @ X22))),
% 3.45/3.66      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.45/3.66  thf('37', plain,
% 3.45/3.66      (![X22 : $i]:
% 3.45/3.66         (~ (v1_relat_1 @ X22)
% 3.45/3.66          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 3.45/3.66          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 3.45/3.66      inference('simplify', [status(thm)], ['36'])).
% 3.45/3.66  thf('38', plain,
% 3.45/3.66      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 3.45/3.66        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.45/3.66      inference('sup-', [status(thm)], ['35', '37'])).
% 3.45/3.66  thf('39', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.45/3.66      inference('sup-', [status(thm)], ['13', '14'])).
% 3.45/3.66  thf(fc4_funct_1, axiom,
% 3.45/3.66    (![A:$i]:
% 3.45/3.66     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.45/3.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.45/3.66  thf('40', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 3.45/3.66      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.45/3.66  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.45/3.66      inference('sup+', [status(thm)], ['39', '40'])).
% 3.45/3.66  thf('42', plain, ((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 3.45/3.66      inference('demod', [status(thm)], ['38', '41'])).
% 3.45/3.66  thf('43', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i]:
% 3.45/3.66         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 3.45/3.66          | ~ (v1_xboole_0 @ X1))),
% 3.45/3.66      inference('sup+', [status(thm)], ['26', '42'])).
% 3.45/3.66  thf('44', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.66         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X2 @ X1 @ X0))
% 3.45/3.66          | ~ (v1_xboole_0 @ X0)
% 3.45/3.66          | ~ (v1_xboole_0 @ X2))),
% 3.45/3.66      inference('sup+', [status(thm)], ['3', '43'])).
% 3.45/3.66  thf('45', plain,
% 3.45/3.66      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.45/3.66        | ~ (v1_xboole_0 @ sk_A)
% 3.45/3.66        | ~ (v1_xboole_0 @ sk_C))),
% 3.45/3.66      inference('sup+', [status(thm)], ['2', '44'])).
% 3.45/3.66  thf('46', plain,
% 3.45/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.45/3.66  thf('47', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.45/3.66      inference('sup-', [status(thm)], ['13', '14'])).
% 3.45/3.66  thf('48', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 3.45/3.66      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.45/3.66  thf('49', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.45/3.66      inference('sup+', [status(thm)], ['47', '48'])).
% 3.45/3.66  thf('50', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('sup+', [status(thm)], ['46', '49'])).
% 3.45/3.66  thf('51', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('52', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.66      inference('split', [status(esa)], ['51'])).
% 3.45/3.66  thf('53', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.66      inference('sup-', [status(thm)], ['50', '52'])).
% 3.45/3.66  thf('54', plain,
% 3.45/3.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.45/3.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.45/3.66        (k6_partfun1 @ sk_A))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('55', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.45/3.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.45/3.66  thf('56', plain,
% 3.45/3.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.45/3.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.45/3.66        (k6_relat_1 @ sk_A))),
% 3.45/3.66      inference('demod', [status(thm)], ['54', '55'])).
% 3.45/3.66  thf('57', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf(t24_funct_2, axiom,
% 3.45/3.66    (![A:$i,B:$i,C:$i]:
% 3.45/3.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.45/3.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.66       ( ![D:$i]:
% 3.45/3.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.45/3.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.45/3.66           ( ( r2_relset_1 @
% 3.45/3.66               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.45/3.66               ( k6_partfun1 @ B ) ) =>
% 3.45/3.66             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.45/3.66  thf('58', plain,
% 3.45/3.66      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.45/3.66         (~ (v1_funct_1 @ X32)
% 3.45/3.66          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 3.45/3.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.45/3.66          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 3.45/3.66               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 3.45/3.66               (k6_partfun1 @ X33))
% 3.45/3.66          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 3.45/3.66          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 3.45/3.66          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 3.45/3.66          | ~ (v1_funct_1 @ X35))),
% 3.45/3.66      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.45/3.66  thf('59', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 3.45/3.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.45/3.66  thf('60', plain,
% 3.45/3.66      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.45/3.66         (~ (v1_funct_1 @ X32)
% 3.45/3.66          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 3.45/3.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.45/3.66          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 3.45/3.66               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 3.45/3.66               (k6_relat_1 @ X33))
% 3.45/3.66          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 3.45/3.66          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 3.45/3.66          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 3.45/3.66          | ~ (v1_funct_1 @ X35))),
% 3.45/3.66      inference('demod', [status(thm)], ['58', '59'])).
% 3.45/3.66  thf('61', plain,
% 3.45/3.66      (![X0 : $i]:
% 3.45/3.66         (~ (v1_funct_1 @ X0)
% 3.45/3.66          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.45/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.45/3.66          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.45/3.66          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.45/3.66               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.45/3.66               (k6_relat_1 @ sk_A))
% 3.45/3.66          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.45/3.66          | ~ (v1_funct_1 @ sk_C))),
% 3.45/3.66      inference('sup-', [status(thm)], ['57', '60'])).
% 3.45/3.66  thf('62', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('64', plain,
% 3.45/3.66      (![X0 : $i]:
% 3.45/3.66         (~ (v1_funct_1 @ X0)
% 3.45/3.66          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.45/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.45/3.66          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.45/3.66          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.45/3.66               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.45/3.66               (k6_relat_1 @ sk_A)))),
% 3.45/3.66      inference('demod', [status(thm)], ['61', '62', '63'])).
% 3.45/3.66  thf('65', plain,
% 3.45/3.66      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.45/3.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.45/3.66        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.45/3.66        | ~ (v1_funct_1 @ sk_D))),
% 3.45/3.66      inference('sup-', [status(thm)], ['56', '64'])).
% 3.45/3.66  thf('66', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('67', plain,
% 3.45/3.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.45/3.66         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.45/3.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.45/3.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.45/3.66  thf('68', plain,
% 3.45/3.66      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.45/3.66      inference('sup-', [status(thm)], ['66', '67'])).
% 3.45/3.66  thf('69', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('72', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.45/3.66      inference('demod', [status(thm)], ['65', '68', '69', '70', '71'])).
% 3.45/3.66  thf('73', plain,
% 3.45/3.66      (![X22 : $i]:
% 3.45/3.66         (~ (v1_relat_1 @ X22)
% 3.45/3.66          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 3.45/3.66          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 3.45/3.66      inference('simplify', [status(thm)], ['36'])).
% 3.45/3.66  thf('74', plain,
% 3.45/3.66      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.45/3.66        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.45/3.66        | ~ (v1_relat_1 @ sk_D))),
% 3.45/3.66      inference('sup-', [status(thm)], ['72', '73'])).
% 3.45/3.66  thf('75', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('76', plain,
% 3.45/3.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.45/3.66         ((v5_relat_1 @ X11 @ X13)
% 3.45/3.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.45/3.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.45/3.66  thf('77', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.45/3.66      inference('sup-', [status(thm)], ['75', '76'])).
% 3.45/3.66  thf('78', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.45/3.66      inference('demod', [status(thm)], ['65', '68', '69', '70', '71'])).
% 3.45/3.66  thf('79', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf(cc1_relset_1, axiom,
% 3.45/3.66    (![A:$i,B:$i,C:$i]:
% 3.45/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.66       ( v1_relat_1 @ C ) ))).
% 3.45/3.66  thf('80', plain,
% 3.45/3.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.45/3.66         ((v1_relat_1 @ X8)
% 3.45/3.66          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 3.45/3.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.45/3.66  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 3.45/3.66      inference('sup-', [status(thm)], ['79', '80'])).
% 3.45/3.66  thf('82', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.45/3.66      inference('demod', [status(thm)], ['74', '77', '78', '81'])).
% 3.45/3.66  thf('83', plain,
% 3.45/3.66      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.45/3.66      inference('split', [status(esa)], ['51'])).
% 3.45/3.66  thf('84', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.45/3.66      inference('sup-', [status(thm)], ['82', '83'])).
% 3.45/3.66  thf('85', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.45/3.66      inference('split', [status(esa)], ['51'])).
% 3.45/3.66  thf('86', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.45/3.66      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 3.45/3.66  thf('87', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.45/3.66      inference('simpl_trail', [status(thm)], ['53', '86'])).
% 3.45/3.66  thf('88', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.45/3.66      inference('clc', [status(thm)], ['45', '87'])).
% 3.45/3.66  thf('89', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i]:
% 3.45/3.66         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.45/3.66      inference('sup+', [status(thm)], ['21', '22'])).
% 3.45/3.66  thf('90', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('91', plain,
% 3.45/3.66      (![X4 : $i, X5 : $i]:
% 3.45/3.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.45/3.66          | (v1_xboole_0 @ X4)
% 3.45/3.66          | ~ (v1_xboole_0 @ X5))),
% 3.45/3.66      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.45/3.66  thf('92', plain,
% 3.45/3.66      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.45/3.66      inference('sup-', [status(thm)], ['90', '91'])).
% 3.45/3.66  thf('93', plain,
% 3.45/3.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.45/3.66        | ~ (v1_xboole_0 @ sk_A)
% 3.45/3.66        | (v1_xboole_0 @ sk_C))),
% 3.45/3.66      inference('sup-', [status(thm)], ['89', '92'])).
% 3.45/3.66  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.45/3.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.45/3.66  thf('95', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.45/3.66      inference('demod', [status(thm)], ['93', '94'])).
% 3.45/3.66  thf('96', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.45/3.66      inference('clc', [status(thm)], ['88', '95'])).
% 3.45/3.66  thf('97', plain,
% 3.45/3.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.45/3.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.45/3.66        (k6_relat_1 @ sk_A))),
% 3.45/3.66      inference('demod', [status(thm)], ['54', '55'])).
% 3.45/3.66  thf('98', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('99', plain,
% 3.45/3.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf(dt_k1_partfun1, axiom,
% 3.45/3.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.45/3.66     ( ( ( v1_funct_1 @ E ) & 
% 3.45/3.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.45/3.66         ( v1_funct_1 @ F ) & 
% 3.45/3.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.45/3.66       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.45/3.66         ( m1_subset_1 @
% 3.45/3.66           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.45/3.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.45/3.66  thf('100', plain,
% 3.45/3.66      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.45/3.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 3.45/3.66          | ~ (v1_funct_1 @ X23)
% 3.45/3.66          | ~ (v1_funct_1 @ X26)
% 3.45/3.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.45/3.66          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 3.45/3.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 3.45/3.66      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.45/3.66  thf('101', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.45/3.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.45/3.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.45/3.66          | ~ (v1_funct_1 @ X1)
% 3.45/3.66          | ~ (v1_funct_1 @ sk_C))),
% 3.45/3.66      inference('sup-', [status(thm)], ['99', '100'])).
% 3.45/3.66  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('103', plain,
% 3.45/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.45/3.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.45/3.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.45/3.66          | ~ (v1_funct_1 @ X1))),
% 3.45/3.66      inference('demod', [status(thm)], ['101', '102'])).
% 3.45/3.66  thf('104', plain,
% 3.45/3.66      ((~ (v1_funct_1 @ sk_D)
% 3.45/3.66        | (m1_subset_1 @ 
% 3.45/3.66           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.45/3.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.45/3.66      inference('sup-', [status(thm)], ['98', '103'])).
% 3.45/3.66  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.66  thf('106', plain,
% 3.45/3.66      ((m1_subset_1 @ 
% 3.45/3.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.45/3.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.45/3.66      inference('demod', [status(thm)], ['104', '105'])).
% 3.45/3.66  thf(redefinition_r2_relset_1, axiom,
% 3.45/3.66    (![A:$i,B:$i,C:$i,D:$i]:
% 3.45/3.66     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.45/3.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.66       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.45/3.66  thf('107', plain,
% 3.45/3.66      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.45/3.66         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.45/3.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.45/3.66          | ((X17) = (X20))
% 3.45/3.66          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 3.45/3.66      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.45/3.66  thf('108', plain,
% 3.45/3.66      (![X0 : $i]:
% 3.45/3.66         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.45/3.66             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.45/3.66          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.45/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.45/3.66      inference('sup-', [status(thm)], ['106', '107'])).
% 3.45/3.66  thf('109', plain,
% 3.45/3.66      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.45/3.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.45/3.66        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.45/3.66            = (k6_relat_1 @ sk_A)))),
% 3.45/3.66      inference('sup-', [status(thm)], ['97', '108'])).
% 3.45/3.66  thf('110', plain,
% 3.45/3.66      (![X30 : $i]:
% 3.45/3.66         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 3.45/3.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 3.45/3.66      inference('demod', [status(thm)], ['6', '7'])).
% 3.45/3.66  thf('111', plain,
% 3.45/3.66      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.45/3.66         = (k6_relat_1 @ sk_A))),
% 3.45/3.67      inference('demod', [status(thm)], ['109', '110'])).
% 3.45/3.67  thf('112', plain,
% 3.45/3.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.67  thf(t26_funct_2, axiom,
% 3.45/3.67    (![A:$i,B:$i,C:$i,D:$i]:
% 3.45/3.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.45/3.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.67       ( ![E:$i]:
% 3.45/3.67         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.45/3.67             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.45/3.67           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.45/3.67             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.45/3.67               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.45/3.67  thf('113', plain,
% 3.45/3.67      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 3.45/3.67         (~ (v1_funct_1 @ X36)
% 3.45/3.67          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 3.45/3.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.45/3.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 3.45/3.67          | (v2_funct_1 @ X40)
% 3.45/3.67          | ((X38) = (k1_xboole_0))
% 3.45/3.67          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 3.45/3.67          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 3.45/3.67          | ~ (v1_funct_1 @ X40))),
% 3.45/3.67      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.45/3.67  thf('114', plain,
% 3.45/3.67      (![X0 : $i, X1 : $i]:
% 3.45/3.67         (~ (v1_funct_1 @ X0)
% 3.45/3.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.45/3.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.45/3.67          | ((sk_A) = (k1_xboole_0))
% 3.45/3.67          | (v2_funct_1 @ X0)
% 3.45/3.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.45/3.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.45/3.67          | ~ (v1_funct_1 @ sk_D))),
% 3.45/3.67      inference('sup-', [status(thm)], ['112', '113'])).
% 3.45/3.67  thf('115', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.45/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.67  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.67  thf('117', plain,
% 3.45/3.67      (![X0 : $i, X1 : $i]:
% 3.45/3.67         (~ (v1_funct_1 @ X0)
% 3.45/3.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.45/3.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.45/3.67          | ((sk_A) = (k1_xboole_0))
% 3.45/3.67          | (v2_funct_1 @ X0)
% 3.45/3.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.45/3.67      inference('demod', [status(thm)], ['114', '115', '116'])).
% 3.45/3.67  thf('118', plain,
% 3.45/3.67      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.45/3.67        | (v2_funct_1 @ sk_C)
% 3.45/3.67        | ((sk_A) = (k1_xboole_0))
% 3.45/3.67        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.45/3.67        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.45/3.67        | ~ (v1_funct_1 @ sk_C))),
% 3.45/3.67      inference('sup-', [status(thm)], ['111', '117'])).
% 3.45/3.67  thf('119', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 3.45/3.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.45/3.67  thf('120', plain,
% 3.45/3.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.67  thf('121', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.45/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.67  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 3.45/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.67  thf('123', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.45/3.67      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 3.45/3.67  thf('124', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.67      inference('split', [status(esa)], ['51'])).
% 3.45/3.67  thf('125', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.45/3.67      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 3.45/3.67  thf('126', plain, (~ (v2_funct_1 @ sk_C)),
% 3.45/3.67      inference('simpl_trail', [status(thm)], ['124', '125'])).
% 3.45/3.67  thf('127', plain, (((sk_A) = (k1_xboole_0))),
% 3.45/3.67      inference('clc', [status(thm)], ['123', '126'])).
% 3.45/3.67  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.45/3.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.45/3.67  thf('129', plain, ($false),
% 3.45/3.67      inference('demod', [status(thm)], ['96', '127', '128'])).
% 3.45/3.67  
% 3.45/3.67  % SZS output end Refutation
% 3.45/3.67  
% 3.45/3.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
