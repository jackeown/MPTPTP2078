%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cQzMkrllVZ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:10 EST 2020

% Result     : Theorem 3.23s
% Output     : Refutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 408 expanded)
%              Number of leaves         :   39 ( 136 expanded)
%              Depth                    :   16
%              Number of atoms          : 1339 (7015 expanded)
%              Number of equality atoms :   58 ( 144 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('4',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_relset_1 @ X1 @ X0 @ X2 )
        = ( k2_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','12'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf('33',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','38'])).

thf('40',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('43',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('44',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('45',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['58','61','62','63','64'])).

thf('66',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('67',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['58','61','62','63','64'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['67','70','71','74'])).

thf('76',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('77',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('79',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['50','79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('86',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('87',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('88',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['81','95'])).

thf('97',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
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
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('111',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35 ) )
      | ( v2_funct_1 @ X39 )
      | ( X37 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    ! [X4: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

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
    inference(split,[status(esa)],['48'])).

thf('125',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cQzMkrllVZ
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:11:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.23/3.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.23/3.41  % Solved by: fo/fo7.sh
% 3.23/3.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.23/3.41  % done 3261 iterations in 2.955s
% 3.23/3.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.23/3.41  % SZS output start Refutation
% 3.23/3.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.23/3.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.23/3.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.23/3.41  thf(sk_C_type, type, sk_C: $i).
% 3.23/3.41  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.23/3.41  thf(sk_B_type, type, sk_B: $i).
% 3.23/3.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.23/3.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.23/3.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.23/3.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.23/3.41  thf(sk_D_type, type, sk_D: $i).
% 3.23/3.41  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.23/3.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.23/3.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.23/3.41  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.23/3.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.23/3.41  thf(sk_A_type, type, sk_A: $i).
% 3.23/3.41  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.23/3.41  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.23/3.41  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.23/3.41  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.23/3.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.23/3.41  thf(t29_funct_2, conjecture,
% 3.23/3.41    (![A:$i,B:$i,C:$i]:
% 3.23/3.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.23/3.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.23/3.41       ( ![D:$i]:
% 3.23/3.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.23/3.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.23/3.41           ( ( r2_relset_1 @
% 3.23/3.41               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.23/3.41               ( k6_partfun1 @ A ) ) =>
% 3.23/3.41             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.23/3.41  thf(zf_stmt_0, negated_conjecture,
% 3.23/3.41    (~( ![A:$i,B:$i,C:$i]:
% 3.23/3.41        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.23/3.41            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.23/3.41          ( ![D:$i]:
% 3.23/3.41            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.23/3.41                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.23/3.41              ( ( r2_relset_1 @
% 3.23/3.41                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.23/3.41                  ( k6_partfun1 @ A ) ) =>
% 3.23/3.41                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.23/3.41    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.23/3.41  thf('0', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf(redefinition_k2_relset_1, axiom,
% 3.23/3.41    (![A:$i,B:$i,C:$i]:
% 3.23/3.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.23/3.41       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.23/3.41  thf('1', plain,
% 3.23/3.41      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.23/3.41         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.23/3.41          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.23/3.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.23/3.41  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.23/3.41      inference('sup-', [status(thm)], ['0', '1'])).
% 3.23/3.41  thf(l13_xboole_0, axiom,
% 3.23/3.41    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.23/3.41  thf('3', plain,
% 3.23/3.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.41  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.23/3.41  thf('4', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.23/3.41      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.23/3.41  thf(redefinition_k6_partfun1, axiom,
% 3.23/3.41    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.23/3.41  thf('5', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 3.23/3.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.23/3.41  thf('6', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.23/3.41      inference('demod', [status(thm)], ['4', '5'])).
% 3.23/3.41  thf(t29_relset_1, axiom,
% 3.23/3.41    (![A:$i]:
% 3.23/3.41     ( m1_subset_1 @
% 3.23/3.41       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.23/3.41  thf('7', plain,
% 3.23/3.41      (![X21 : $i]:
% 3.23/3.41         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 3.23/3.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.23/3.41      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.23/3.41  thf('8', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 3.23/3.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.23/3.41  thf('9', plain,
% 3.23/3.41      (![X21 : $i]:
% 3.23/3.41         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.23/3.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.23/3.41      inference('demod', [status(thm)], ['7', '8'])).
% 3.23/3.41  thf('10', plain,
% 3.23/3.41      ((m1_subset_1 @ k1_xboole_0 @ 
% 3.23/3.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.23/3.41      inference('sup+', [status(thm)], ['6', '9'])).
% 3.23/3.41  thf(t113_zfmisc_1, axiom,
% 3.23/3.41    (![A:$i,B:$i]:
% 3.23/3.41     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.23/3.41       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.23/3.41  thf('11', plain,
% 3.23/3.41      (![X2 : $i, X3 : $i]:
% 3.23/3.41         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 3.23/3.41      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.23/3.41  thf('12', plain,
% 3.23/3.41      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.23/3.41      inference('simplify', [status(thm)], ['11'])).
% 3.23/3.41  thf('13', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.23/3.41      inference('demod', [status(thm)], ['10', '12'])).
% 3.23/3.41  thf('14', plain,
% 3.23/3.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.41  thf('15', plain,
% 3.23/3.41      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.23/3.41      inference('simplify', [status(thm)], ['11'])).
% 3.23/3.41  thf('16', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('sup+', [status(thm)], ['14', '15'])).
% 3.23/3.41  thf('17', plain,
% 3.23/3.41      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.23/3.41         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.23/3.41          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.23/3.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.23/3.41  thf('18', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.23/3.41         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.23/3.41          | ~ (v1_xboole_0 @ X1)
% 3.23/3.41          | ((k2_relset_1 @ X1 @ X0 @ X2) = (k2_relat_1 @ X2)))),
% 3.23/3.41      inference('sup-', [status(thm)], ['16', '17'])).
% 3.23/3.41  thf('19', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         (((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 3.23/3.41          | ~ (v1_xboole_0 @ X1))),
% 3.23/3.41      inference('sup-', [status(thm)], ['13', '18'])).
% 3.23/3.41  thf('20', plain,
% 3.23/3.41      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.23/3.41      inference('simplify', [status(thm)], ['11'])).
% 3.23/3.41  thf('21', plain,
% 3.23/3.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.41  thf('22', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.23/3.41      inference('demod', [status(thm)], ['10', '12'])).
% 3.23/3.41  thf('23', plain,
% 3.23/3.41      (![X0 : $i]:
% 3.23/3.41         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.23/3.41          | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('sup+', [status(thm)], ['21', '22'])).
% 3.23/3.41  thf(cc2_relset_1, axiom,
% 3.23/3.41    (![A:$i,B:$i,C:$i]:
% 3.23/3.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.23/3.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.23/3.41  thf('24', plain,
% 3.23/3.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.23/3.41         ((v5_relat_1 @ X8 @ X10)
% 3.23/3.41          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 3.23/3.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.23/3.41  thf('25', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.23/3.41          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.23/3.41      inference('sup-', [status(thm)], ['23', '24'])).
% 3.23/3.41  thf('26', plain,
% 3.23/3.41      (![X0 : $i]:
% 3.23/3.41         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 3.23/3.41      inference('sup-', [status(thm)], ['20', '25'])).
% 3.23/3.41  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.23/3.41  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.23/3.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.23/3.41  thf('28', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 3.23/3.41      inference('demod', [status(thm)], ['26', '27'])).
% 3.23/3.41  thf(d3_funct_2, axiom,
% 3.23/3.41    (![A:$i,B:$i]:
% 3.23/3.41     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.23/3.41       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.23/3.41  thf('29', plain,
% 3.23/3.41      (![X22 : $i, X23 : $i]:
% 3.23/3.41         (((k2_relat_1 @ X23) != (X22))
% 3.23/3.41          | (v2_funct_2 @ X23 @ X22)
% 3.23/3.41          | ~ (v5_relat_1 @ X23 @ X22)
% 3.23/3.41          | ~ (v1_relat_1 @ X23))),
% 3.23/3.41      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.23/3.41  thf('30', plain,
% 3.23/3.41      (![X23 : $i]:
% 3.23/3.41         (~ (v1_relat_1 @ X23)
% 3.23/3.41          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 3.23/3.41          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 3.23/3.41      inference('simplify', [status(thm)], ['29'])).
% 3.23/3.41  thf('31', plain,
% 3.23/3.41      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 3.23/3.41        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.23/3.41      inference('sup-', [status(thm)], ['28', '30'])).
% 3.23/3.41  thf('32', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.23/3.41      inference('demod', [status(thm)], ['4', '5'])).
% 3.23/3.41  thf('33', plain,
% 3.23/3.41      (![X21 : $i]:
% 3.23/3.41         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.23/3.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.23/3.41      inference('demod', [status(thm)], ['7', '8'])).
% 3.23/3.41  thf(cc1_relset_1, axiom,
% 3.23/3.41    (![A:$i,B:$i,C:$i]:
% 3.23/3.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.23/3.41       ( v1_relat_1 @ C ) ))).
% 3.23/3.41  thf('34', plain,
% 3.23/3.41      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.23/3.41         ((v1_relat_1 @ X5)
% 3.23/3.41          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.23/3.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.23/3.41  thf('35', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 3.23/3.41      inference('sup-', [status(thm)], ['33', '34'])).
% 3.23/3.41  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.23/3.41      inference('sup+', [status(thm)], ['32', '35'])).
% 3.23/3.41  thf('37', plain, ((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 3.23/3.41      inference('demod', [status(thm)], ['31', '36'])).
% 3.23/3.41  thf('38', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 3.23/3.41          | ~ (v1_xboole_0 @ X1))),
% 3.23/3.41      inference('sup+', [status(thm)], ['19', '37'])).
% 3.23/3.41  thf('39', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.23/3.41         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X2 @ X1 @ X0))
% 3.23/3.41          | ~ (v1_xboole_0 @ X0)
% 3.23/3.41          | ~ (v1_xboole_0 @ X2))),
% 3.23/3.41      inference('sup+', [status(thm)], ['3', '38'])).
% 3.23/3.41  thf('40', plain,
% 3.23/3.41      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.23/3.41        | ~ (v1_xboole_0 @ sk_A)
% 3.23/3.41        | ~ (v1_xboole_0 @ sk_C))),
% 3.23/3.41      inference('sup+', [status(thm)], ['2', '39'])).
% 3.23/3.41  thf('41', plain,
% 3.23/3.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.41  thf('42', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.23/3.41      inference('demod', [status(thm)], ['4', '5'])).
% 3.23/3.41  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.23/3.41  thf('43', plain, (![X4 : $i]: (v2_funct_1 @ (k6_relat_1 @ X4))),
% 3.23/3.41      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.23/3.41  thf('44', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 3.23/3.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.23/3.41  thf('45', plain, (![X4 : $i]: (v2_funct_1 @ (k6_partfun1 @ X4))),
% 3.23/3.41      inference('demod', [status(thm)], ['43', '44'])).
% 3.23/3.41  thf('46', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.23/3.41      inference('sup+', [status(thm)], ['42', '45'])).
% 3.23/3.41  thf('47', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('sup+', [status(thm)], ['41', '46'])).
% 3.23/3.41  thf('48', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('49', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.23/3.41      inference('split', [status(esa)], ['48'])).
% 3.23/3.41  thf('50', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.23/3.41      inference('sup-', [status(thm)], ['47', '49'])).
% 3.23/3.41  thf('51', plain,
% 3.23/3.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.23/3.41        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.23/3.41        (k6_partfun1 @ sk_A))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('52', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf(t24_funct_2, axiom,
% 3.23/3.41    (![A:$i,B:$i,C:$i]:
% 3.23/3.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.23/3.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.23/3.41       ( ![D:$i]:
% 3.23/3.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.23/3.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.23/3.41           ( ( r2_relset_1 @
% 3.23/3.41               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.23/3.41               ( k6_partfun1 @ B ) ) =>
% 3.23/3.41             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.23/3.41  thf('53', plain,
% 3.23/3.41      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.23/3.41         (~ (v1_funct_1 @ X31)
% 3.23/3.41          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 3.23/3.41          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.23/3.41          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 3.23/3.41               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 3.23/3.41               (k6_partfun1 @ X32))
% 3.23/3.41          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 3.23/3.41          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.23/3.41          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 3.23/3.41          | ~ (v1_funct_1 @ X34))),
% 3.23/3.41      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.23/3.41  thf('54', plain,
% 3.23/3.41      (![X0 : $i]:
% 3.23/3.41         (~ (v1_funct_1 @ X0)
% 3.23/3.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.23/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.23/3.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.23/3.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.23/3.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.23/3.41               (k6_partfun1 @ sk_A))
% 3.23/3.41          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.23/3.41          | ~ (v1_funct_1 @ sk_C))),
% 3.23/3.41      inference('sup-', [status(thm)], ['52', '53'])).
% 3.23/3.41  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('57', plain,
% 3.23/3.41      (![X0 : $i]:
% 3.23/3.41         (~ (v1_funct_1 @ X0)
% 3.23/3.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.23/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.23/3.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.23/3.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.23/3.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.23/3.41               (k6_partfun1 @ sk_A)))),
% 3.23/3.41      inference('demod', [status(thm)], ['54', '55', '56'])).
% 3.23/3.41  thf('58', plain,
% 3.23/3.41      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.23/3.41        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.23/3.41        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.23/3.41        | ~ (v1_funct_1 @ sk_D))),
% 3.23/3.41      inference('sup-', [status(thm)], ['51', '57'])).
% 3.23/3.41  thf('59', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('60', plain,
% 3.23/3.41      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.23/3.41         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.23/3.41          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.23/3.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.23/3.41  thf('61', plain,
% 3.23/3.41      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.23/3.41      inference('sup-', [status(thm)], ['59', '60'])).
% 3.23/3.41  thf('62', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('63', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('65', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.23/3.41      inference('demod', [status(thm)], ['58', '61', '62', '63', '64'])).
% 3.23/3.41  thf('66', plain,
% 3.23/3.41      (![X23 : $i]:
% 3.23/3.41         (~ (v1_relat_1 @ X23)
% 3.23/3.41          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 3.23/3.41          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 3.23/3.41      inference('simplify', [status(thm)], ['29'])).
% 3.23/3.41  thf('67', plain,
% 3.23/3.41      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.23/3.41        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.23/3.41        | ~ (v1_relat_1 @ sk_D))),
% 3.23/3.41      inference('sup-', [status(thm)], ['65', '66'])).
% 3.23/3.41  thf('68', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('69', plain,
% 3.23/3.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.23/3.41         ((v5_relat_1 @ X8 @ X10)
% 3.23/3.41          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 3.23/3.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.23/3.41  thf('70', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.23/3.41      inference('sup-', [status(thm)], ['68', '69'])).
% 3.23/3.41  thf('71', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.23/3.41      inference('demod', [status(thm)], ['58', '61', '62', '63', '64'])).
% 3.23/3.41  thf('72', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('73', plain,
% 3.23/3.41      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.23/3.41         ((v1_relat_1 @ X5)
% 3.23/3.41          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.23/3.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.23/3.41  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 3.23/3.41      inference('sup-', [status(thm)], ['72', '73'])).
% 3.23/3.41  thf('75', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.23/3.41      inference('demod', [status(thm)], ['67', '70', '71', '74'])).
% 3.23/3.41  thf('76', plain,
% 3.23/3.41      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.23/3.41      inference('split', [status(esa)], ['48'])).
% 3.23/3.41  thf('77', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.23/3.41      inference('sup-', [status(thm)], ['75', '76'])).
% 3.23/3.41  thf('78', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.23/3.41      inference('split', [status(esa)], ['48'])).
% 3.23/3.41  thf('79', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.23/3.41      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 3.23/3.41  thf('80', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.23/3.41      inference('simpl_trail', [status(thm)], ['50', '79'])).
% 3.23/3.41  thf('81', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.23/3.41      inference('clc', [status(thm)], ['40', '80'])).
% 3.23/3.41  thf('82', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('sup+', [status(thm)], ['14', '15'])).
% 3.23/3.41  thf('83', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('84', plain,
% 3.23/3.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.41  thf('85', plain,
% 3.23/3.41      (![X2 : $i, X3 : $i]:
% 3.23/3.41         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.23/3.41      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.23/3.41  thf('86', plain,
% 3.23/3.41      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 3.23/3.41      inference('simplify', [status(thm)], ['85'])).
% 3.23/3.41  thf(cc4_relset_1, axiom,
% 3.23/3.41    (![A:$i,B:$i]:
% 3.23/3.41     ( ( v1_xboole_0 @ A ) =>
% 3.23/3.41       ( ![C:$i]:
% 3.23/3.41         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 3.23/3.41           ( v1_xboole_0 @ C ) ) ) ))).
% 3.23/3.41  thf('87', plain,
% 3.23/3.41      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.23/3.41         (~ (v1_xboole_0 @ X11)
% 3.23/3.41          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 3.23/3.41          | (v1_xboole_0 @ X12))),
% 3.23/3.41      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.23/3.41  thf('88', plain,
% 3.23/3.41      (![X1 : $i]:
% 3.23/3.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.23/3.41          | (v1_xboole_0 @ X1)
% 3.23/3.41          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.23/3.41      inference('sup-', [status(thm)], ['86', '87'])).
% 3.23/3.41  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.23/3.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.23/3.41  thf('90', plain,
% 3.23/3.41      (![X1 : $i]:
% 3.23/3.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.23/3.41          | (v1_xboole_0 @ X1))),
% 3.23/3.41      inference('demod', [status(thm)], ['88', '89'])).
% 3.23/3.41  thf('91', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 3.23/3.41          | ~ (v1_xboole_0 @ X0)
% 3.23/3.41          | (v1_xboole_0 @ X1))),
% 3.23/3.41      inference('sup-', [status(thm)], ['84', '90'])).
% 3.23/3.41  thf('92', plain,
% 3.23/3.41      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.23/3.41      inference('sup-', [status(thm)], ['83', '91'])).
% 3.23/3.41  thf('93', plain,
% 3.23/3.41      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.23/3.41        | ~ (v1_xboole_0 @ sk_A)
% 3.23/3.41        | (v1_xboole_0 @ sk_C))),
% 3.23/3.41      inference('sup-', [status(thm)], ['82', '92'])).
% 3.23/3.41  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.23/3.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.23/3.41  thf('95', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.23/3.41      inference('demod', [status(thm)], ['93', '94'])).
% 3.23/3.41  thf('96', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.23/3.41      inference('clc', [status(thm)], ['81', '95'])).
% 3.23/3.41  thf('97', plain,
% 3.23/3.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.23/3.41        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.23/3.41        (k6_partfun1 @ sk_A))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('98', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('99', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf(dt_k1_partfun1, axiom,
% 3.23/3.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.23/3.41     ( ( ( v1_funct_1 @ E ) & 
% 3.23/3.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.23/3.41         ( v1_funct_1 @ F ) & 
% 3.23/3.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.23/3.41       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.23/3.41         ( m1_subset_1 @
% 3.23/3.41           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.23/3.41           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.23/3.41  thf('100', plain,
% 3.23/3.41      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.23/3.41         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.23/3.41          | ~ (v1_funct_1 @ X24)
% 3.23/3.41          | ~ (v1_funct_1 @ X27)
% 3.23/3.41          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.23/3.41          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 3.23/3.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 3.23/3.41      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.23/3.41  thf('101', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.23/3.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.23/3.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.23/3.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.23/3.41          | ~ (v1_funct_1 @ X1)
% 3.23/3.41          | ~ (v1_funct_1 @ sk_C))),
% 3.23/3.41      inference('sup-', [status(thm)], ['99', '100'])).
% 3.23/3.41  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('103', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.23/3.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.23/3.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.23/3.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.23/3.41          | ~ (v1_funct_1 @ X1))),
% 3.23/3.41      inference('demod', [status(thm)], ['101', '102'])).
% 3.23/3.41  thf('104', plain,
% 3.23/3.41      ((~ (v1_funct_1 @ sk_D)
% 3.23/3.41        | (m1_subset_1 @ 
% 3.23/3.41           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.23/3.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.23/3.41      inference('sup-', [status(thm)], ['98', '103'])).
% 3.23/3.41  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('106', plain,
% 3.23/3.41      ((m1_subset_1 @ 
% 3.23/3.41        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.23/3.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.23/3.41      inference('demod', [status(thm)], ['104', '105'])).
% 3.23/3.41  thf(redefinition_r2_relset_1, axiom,
% 3.23/3.41    (![A:$i,B:$i,C:$i,D:$i]:
% 3.23/3.41     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.23/3.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.23/3.41       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.23/3.41  thf('107', plain,
% 3.23/3.41      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.23/3.41         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.23/3.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.23/3.41          | ((X17) = (X20))
% 3.23/3.41          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 3.23/3.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.23/3.41  thf('108', plain,
% 3.23/3.41      (![X0 : $i]:
% 3.23/3.41         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.23/3.41             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.23/3.41          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.23/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.23/3.41      inference('sup-', [status(thm)], ['106', '107'])).
% 3.23/3.41  thf('109', plain,
% 3.23/3.41      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.23/3.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.23/3.41        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.23/3.41            = (k6_partfun1 @ sk_A)))),
% 3.23/3.41      inference('sup-', [status(thm)], ['97', '108'])).
% 3.23/3.41  thf('110', plain,
% 3.23/3.41      (![X21 : $i]:
% 3.23/3.41         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.23/3.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.23/3.41      inference('demod', [status(thm)], ['7', '8'])).
% 3.23/3.41  thf('111', plain,
% 3.23/3.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.23/3.41         = (k6_partfun1 @ sk_A))),
% 3.23/3.41      inference('demod', [status(thm)], ['109', '110'])).
% 3.23/3.41  thf('112', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf(t26_funct_2, axiom,
% 3.23/3.41    (![A:$i,B:$i,C:$i,D:$i]:
% 3.23/3.41     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.23/3.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.23/3.41       ( ![E:$i]:
% 3.23/3.41         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.23/3.41             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.23/3.41           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.23/3.41             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.23/3.41               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.23/3.41  thf('113', plain,
% 3.23/3.41      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 3.23/3.41         (~ (v1_funct_1 @ X35)
% 3.23/3.41          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.23/3.41          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.23/3.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35))
% 3.23/3.41          | (v2_funct_1 @ X39)
% 3.23/3.41          | ((X37) = (k1_xboole_0))
% 3.23/3.41          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 3.23/3.41          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 3.23/3.41          | ~ (v1_funct_1 @ X39))),
% 3.23/3.41      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.23/3.41  thf('114', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         (~ (v1_funct_1 @ X0)
% 3.23/3.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.23/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.23/3.41          | ((sk_A) = (k1_xboole_0))
% 3.23/3.41          | (v2_funct_1 @ X0)
% 3.23/3.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.23/3.41          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.23/3.41          | ~ (v1_funct_1 @ sk_D))),
% 3.23/3.41      inference('sup-', [status(thm)], ['112', '113'])).
% 3.23/3.41  thf('115', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('117', plain,
% 3.23/3.41      (![X0 : $i, X1 : $i]:
% 3.23/3.41         (~ (v1_funct_1 @ X0)
% 3.23/3.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.23/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.23/3.41          | ((sk_A) = (k1_xboole_0))
% 3.23/3.41          | (v2_funct_1 @ X0)
% 3.23/3.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.23/3.41      inference('demod', [status(thm)], ['114', '115', '116'])).
% 3.23/3.41  thf('118', plain,
% 3.23/3.41      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.23/3.41        | (v2_funct_1 @ sk_C)
% 3.23/3.41        | ((sk_A) = (k1_xboole_0))
% 3.23/3.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.23/3.41        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.23/3.41        | ~ (v1_funct_1 @ sk_C))),
% 3.23/3.41      inference('sup-', [status(thm)], ['111', '117'])).
% 3.23/3.41  thf('119', plain, (![X4 : $i]: (v2_funct_1 @ (k6_partfun1 @ X4))),
% 3.23/3.41      inference('demod', [status(thm)], ['43', '44'])).
% 3.23/3.41  thf('120', plain,
% 3.23/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('121', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 3.23/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.41  thf('123', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.23/3.41      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 3.23/3.41  thf('124', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.23/3.41      inference('split', [status(esa)], ['48'])).
% 3.23/3.41  thf('125', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.23/3.41      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 3.23/3.41  thf('126', plain, (~ (v2_funct_1 @ sk_C)),
% 3.23/3.41      inference('simpl_trail', [status(thm)], ['124', '125'])).
% 3.23/3.41  thf('127', plain, (((sk_A) = (k1_xboole_0))),
% 3.23/3.41      inference('clc', [status(thm)], ['123', '126'])).
% 3.23/3.41  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.23/3.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.23/3.41  thf('129', plain, ($false),
% 3.23/3.41      inference('demod', [status(thm)], ['96', '127', '128'])).
% 3.23/3.41  
% 3.23/3.41  % SZS output end Refutation
% 3.23/3.41  
% 3.25/3.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
