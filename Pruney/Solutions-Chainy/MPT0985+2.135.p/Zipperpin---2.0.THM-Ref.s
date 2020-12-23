%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A3m2aSclsS

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:46 EST 2020

% Result     : Theorem 2.89s
% Output     : Refutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 489 expanded)
%              Number of leaves         :   34 ( 155 expanded)
%              Depth                    :   18
%              Number of atoms          : 1326 (7651 expanded)
%              Number of equality atoms :   66 ( 316 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['32','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('67',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X26: $i] :
      ( ( v1_funct_2 @ X26 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['63','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','83'])).

thf('85',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','84'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','85','86'])).

thf('88',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('92',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('94',plain,(
    ! [X26: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['90','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['89','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('110',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('112',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('114',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','85','86'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','116','117','118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['88','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A3m2aSclsS
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:34:12 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 2.89/3.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.89/3.07  % Solved by: fo/fo7.sh
% 2.89/3.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.89/3.07  % done 2358 iterations in 2.586s
% 2.89/3.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.89/3.07  % SZS output start Refutation
% 2.89/3.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.89/3.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.89/3.07  thf(sk_A_type, type, sk_A: $i).
% 2.89/3.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.89/3.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.89/3.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.89/3.07  thf(sk_C_type, type, sk_C: $i).
% 2.89/3.07  thf(sk_B_type, type, sk_B: $i).
% 2.89/3.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.89/3.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.89/3.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.89/3.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.89/3.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.89/3.07  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.89/3.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.89/3.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.89/3.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.89/3.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.89/3.07  thf(t31_funct_2, conjecture,
% 2.89/3.07    (![A:$i,B:$i,C:$i]:
% 2.89/3.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.89/3.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.89/3.07       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.89/3.07         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.89/3.07           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.89/3.07           ( m1_subset_1 @
% 2.89/3.07             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.89/3.07  thf(zf_stmt_0, negated_conjecture,
% 2.89/3.07    (~( ![A:$i,B:$i,C:$i]:
% 2.89/3.07        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.89/3.07            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.89/3.07          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.89/3.07            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.89/3.07              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.89/3.07              ( m1_subset_1 @
% 2.89/3.07                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.89/3.07    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.89/3.07  thf('0', plain,
% 2.89/3.07      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.89/3.07        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.89/3.07        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.89/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.07  thf('1', plain,
% 2.89/3.07      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.89/3.07         <= (~
% 2.89/3.07             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.07               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.89/3.07      inference('split', [status(esa)], ['0'])).
% 2.89/3.07  thf('2', plain,
% 2.89/3.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.07  thf(cc1_relset_1, axiom,
% 2.89/3.07    (![A:$i,B:$i,C:$i]:
% 2.89/3.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.07       ( v1_relat_1 @ C ) ))).
% 2.89/3.07  thf('3', plain,
% 2.89/3.07      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.89/3.07         ((v1_relat_1 @ X9)
% 2.89/3.07          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.89/3.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.89/3.07  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 2.89/3.07      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.07  thf(dt_k2_funct_1, axiom,
% 2.89/3.07    (![A:$i]:
% 2.89/3.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.89/3.07       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.89/3.07         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.89/3.07  thf('5', plain,
% 2.89/3.07      (![X6 : $i]:
% 2.89/3.07         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 2.89/3.07          | ~ (v1_funct_1 @ X6)
% 2.89/3.07          | ~ (v1_relat_1 @ X6))),
% 2.89/3.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.89/3.07  thf('6', plain,
% 2.89/3.07      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.89/3.07         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.89/3.07      inference('split', [status(esa)], ['0'])).
% 2.89/3.07  thf('7', plain,
% 2.89/3.07      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 2.89/3.07         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.89/3.07      inference('sup-', [status(thm)], ['5', '6'])).
% 2.89/3.07  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 2.89/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.07  thf('9', plain,
% 2.89/3.07      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.89/3.07      inference('demod', [status(thm)], ['7', '8'])).
% 2.89/3.07  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.89/3.07      inference('sup-', [status(thm)], ['4', '9'])).
% 2.89/3.07  thf('11', plain,
% 2.89/3.07      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.89/3.07         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.89/3.07      inference('split', [status(esa)], ['0'])).
% 2.89/3.07  thf('12', plain,
% 2.89/3.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.07  thf(redefinition_k2_relset_1, axiom,
% 2.89/3.07    (![A:$i,B:$i,C:$i]:
% 2.89/3.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.89/3.07  thf('13', plain,
% 2.89/3.07      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.89/3.07         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.89/3.07          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.89/3.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.89/3.07  thf('14', plain,
% 2.89/3.07      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.89/3.07      inference('sup-', [status(thm)], ['12', '13'])).
% 2.89/3.07  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.89/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.07  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.89/3.07      inference('sup+', [status(thm)], ['14', '15'])).
% 2.89/3.07  thf(d1_funct_2, axiom,
% 2.89/3.07    (![A:$i,B:$i,C:$i]:
% 2.89/3.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.07       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.89/3.07           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.89/3.07             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.89/3.07         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.89/3.07           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.89/3.07             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.89/3.07  thf(zf_stmt_1, axiom,
% 2.89/3.07    (![B:$i,A:$i]:
% 2.89/3.07     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.89/3.07       ( zip_tseitin_0 @ B @ A ) ))).
% 2.89/3.07  thf('17', plain,
% 2.89/3.07      (![X18 : $i, X19 : $i]:
% 2.89/3.07         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 2.89/3.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.89/3.07  thf('18', plain,
% 2.89/3.07      (![X6 : $i]:
% 2.89/3.07         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 2.89/3.07          | ~ (v1_funct_1 @ X6)
% 2.89/3.07          | ~ (v1_relat_1 @ X6))),
% 2.89/3.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.89/3.07  thf(t55_funct_1, axiom,
% 2.89/3.07    (![A:$i]:
% 2.89/3.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.89/3.07       ( ( v2_funct_1 @ A ) =>
% 2.89/3.07         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.89/3.07           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.89/3.07  thf('19', plain,
% 2.89/3.07      (![X7 : $i]:
% 2.89/3.07         (~ (v2_funct_1 @ X7)
% 2.89/3.07          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 2.89/3.07          | ~ (v1_funct_1 @ X7)
% 2.89/3.07          | ~ (v1_relat_1 @ X7))),
% 2.89/3.07      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.89/3.07  thf(t64_relat_1, axiom,
% 2.89/3.07    (![A:$i]:
% 2.89/3.07     ( ( v1_relat_1 @ A ) =>
% 2.89/3.07       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.89/3.07           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.89/3.07         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.89/3.07  thf('20', plain,
% 2.89/3.07      (![X5 : $i]:
% 2.89/3.07         (((k1_relat_1 @ X5) != (k1_xboole_0))
% 2.89/3.07          | ((X5) = (k1_xboole_0))
% 2.89/3.07          | ~ (v1_relat_1 @ X5))),
% 2.89/3.07      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.89/3.07  thf('21', plain,
% 2.89/3.07      (![X0 : $i]:
% 2.89/3.07         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 2.89/3.07          | ~ (v1_relat_1 @ X0)
% 2.89/3.07          | ~ (v1_funct_1 @ X0)
% 2.89/3.07          | ~ (v2_funct_1 @ X0)
% 2.89/3.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.89/3.07          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 2.89/3.07      inference('sup-', [status(thm)], ['19', '20'])).
% 2.89/3.07  thf('22', plain,
% 2.89/3.07      (![X0 : $i]:
% 2.89/3.07         (~ (v1_relat_1 @ X0)
% 2.89/3.07          | ~ (v1_funct_1 @ X0)
% 2.89/3.07          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 2.89/3.07          | ~ (v2_funct_1 @ X0)
% 2.89/3.07          | ~ (v1_funct_1 @ X0)
% 2.89/3.07          | ~ (v1_relat_1 @ X0)
% 2.89/3.07          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 2.89/3.07      inference('sup-', [status(thm)], ['18', '21'])).
% 2.89/3.07  thf('23', plain,
% 2.89/3.07      (![X0 : $i]:
% 2.89/3.07         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0))),
% 2.89/3.08      inference('simplify', [status(thm)], ['22'])).
% 2.89/3.08  thf('24', plain,
% 2.89/3.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.89/3.08         (((k2_relat_1 @ X1) != (X0))
% 2.89/3.08          | (zip_tseitin_0 @ X0 @ X2)
% 2.89/3.08          | ~ (v1_relat_1 @ X1)
% 2.89/3.08          | ~ (v1_funct_1 @ X1)
% 2.89/3.08          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 2.89/3.08          | ~ (v2_funct_1 @ X1))),
% 2.89/3.08      inference('sup-', [status(thm)], ['17', '23'])).
% 2.89/3.08  thf('25', plain,
% 2.89/3.08      (![X1 : $i, X2 : $i]:
% 2.89/3.08         (~ (v2_funct_1 @ X1)
% 2.89/3.08          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 2.89/3.08          | ~ (v1_funct_1 @ X1)
% 2.89/3.08          | ~ (v1_relat_1 @ X1)
% 2.89/3.08          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 2.89/3.08      inference('simplify', [status(thm)], ['24'])).
% 2.89/3.08  thf('26', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((zip_tseitin_0 @ sk_B @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ sk_C)
% 2.89/3.08          | ~ (v1_funct_1 @ sk_C)
% 2.89/3.08          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 2.89/3.08          | ~ (v2_funct_1 @ sk_C))),
% 2.89/3.08      inference('sup+', [status(thm)], ['16', '25'])).
% 2.89/3.08  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 2.89/3.08      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.08  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('30', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 2.89/3.08      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.89/3.08  thf('31', plain,
% 2.89/3.08      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.89/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.89/3.08      inference('split', [status(esa)], ['0'])).
% 2.89/3.08  thf('32', plain,
% 2.89/3.08      ((![X0 : $i]:
% 2.89/3.08          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 2.89/3.08           | (zip_tseitin_0 @ sk_B @ X0)))
% 2.89/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.89/3.08      inference('sup-', [status(thm)], ['30', '31'])).
% 2.89/3.08  thf('33', plain,
% 2.89/3.08      (![X18 : $i, X19 : $i]:
% 2.89/3.08         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.89/3.08  thf(t4_subset_1, axiom,
% 2.89/3.08    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.89/3.08  thf('34', plain,
% 2.89/3.08      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 2.89/3.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.89/3.08  thf(redefinition_k1_relset_1, axiom,
% 2.89/3.08    (![A:$i,B:$i,C:$i]:
% 2.89/3.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.89/3.08  thf('35', plain,
% 2.89/3.08      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.89/3.08         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 2.89/3.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.89/3.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.89/3.08  thf('36', plain,
% 2.89/3.08      (![X0 : $i, X1 : $i]:
% 2.89/3.08         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.89/3.08      inference('sup-', [status(thm)], ['34', '35'])).
% 2.89/3.08  thf(t60_relat_1, axiom,
% 2.89/3.08    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.89/3.08     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.89/3.08  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.89/3.08      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.89/3.08  thf('38', plain,
% 2.89/3.08      (![X0 : $i, X1 : $i]:
% 2.89/3.08         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.89/3.08      inference('demod', [status(thm)], ['36', '37'])).
% 2.89/3.08  thf(zf_stmt_2, axiom,
% 2.89/3.08    (![C:$i,B:$i,A:$i]:
% 2.89/3.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.89/3.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.89/3.08  thf('39', plain,
% 2.89/3.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.89/3.08         (((X20) != (k1_relset_1 @ X20 @ X21 @ X22))
% 2.89/3.08          | (v1_funct_2 @ X22 @ X20 @ X21)
% 2.89/3.08          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.89/3.08  thf('40', plain,
% 2.89/3.08      (![X0 : $i, X1 : $i]:
% 2.89/3.08         (((X1) != (k1_xboole_0))
% 2.89/3.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 2.89/3.08          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 2.89/3.08      inference('sup-', [status(thm)], ['38', '39'])).
% 2.89/3.08  thf('41', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.89/3.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.89/3.08      inference('simplify', [status(thm)], ['40'])).
% 2.89/3.08  thf('42', plain,
% 2.89/3.08      (![X18 : $i, X19 : $i]:
% 2.89/3.08         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.89/3.08  thf('43', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 2.89/3.08      inference('simplify', [status(thm)], ['42'])).
% 2.89/3.08  thf('44', plain,
% 2.89/3.08      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 2.89/3.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.89/3.08  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.89/3.08  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.89/3.08  thf(zf_stmt_5, axiom,
% 2.89/3.08    (![A:$i,B:$i,C:$i]:
% 2.89/3.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.89/3.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.89/3.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.89/3.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.89/3.08  thf('45', plain,
% 2.89/3.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.89/3.08         (~ (zip_tseitin_0 @ X23 @ X24)
% 2.89/3.08          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 2.89/3.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.89/3.08  thf('46', plain,
% 2.89/3.08      (![X0 : $i, X1 : $i]:
% 2.89/3.08         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.89/3.08      inference('sup-', [status(thm)], ['44', '45'])).
% 2.89/3.08  thf('47', plain,
% 2.89/3.08      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.89/3.08      inference('sup-', [status(thm)], ['43', '46'])).
% 2.89/3.08  thf('48', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.89/3.08      inference('demod', [status(thm)], ['41', '47'])).
% 2.89/3.08  thf('49', plain,
% 2.89/3.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.89/3.08         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 2.89/3.08      inference('sup+', [status(thm)], ['33', '48'])).
% 2.89/3.08  thf('50', plain,
% 2.89/3.08      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 2.89/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.89/3.08      inference('clc', [status(thm)], ['32', '49'])).
% 2.89/3.08  thf('51', plain,
% 2.89/3.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('52', plain,
% 2.89/3.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.89/3.08         (~ (zip_tseitin_0 @ X23 @ X24)
% 2.89/3.08          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 2.89/3.08          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.89/3.08  thf('53', plain,
% 2.89/3.08      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.89/3.08      inference('sup-', [status(thm)], ['51', '52'])).
% 2.89/3.08  thf('54', plain,
% 2.89/3.08      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 2.89/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.89/3.08      inference('sup-', [status(thm)], ['50', '53'])).
% 2.89/3.08  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('56', plain,
% 2.89/3.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.89/3.08         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 2.89/3.08          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 2.89/3.08          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.89/3.08  thf('57', plain,
% 2.89/3.08      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.89/3.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.89/3.08      inference('sup-', [status(thm)], ['55', '56'])).
% 2.89/3.08  thf('58', plain,
% 2.89/3.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('59', plain,
% 2.89/3.08      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.89/3.08         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 2.89/3.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.89/3.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.89/3.08  thf('60', plain,
% 2.89/3.08      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.89/3.08      inference('sup-', [status(thm)], ['58', '59'])).
% 2.89/3.08  thf('61', plain,
% 2.89/3.08      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.89/3.08      inference('demod', [status(thm)], ['57', '60'])).
% 2.89/3.08  thf('62', plain,
% 2.89/3.08      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.89/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.89/3.08      inference('sup-', [status(thm)], ['54', '61'])).
% 2.89/3.08  thf('63', plain,
% 2.89/3.08      (![X7 : $i]:
% 2.89/3.08         (~ (v2_funct_1 @ X7)
% 2.89/3.08          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 2.89/3.08          | ~ (v1_funct_1 @ X7)
% 2.89/3.08          | ~ (v1_relat_1 @ X7))),
% 2.89/3.08      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.89/3.08  thf('64', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.89/3.08      inference('sup+', [status(thm)], ['14', '15'])).
% 2.89/3.08  thf('65', plain,
% 2.89/3.08      (![X6 : $i]:
% 2.89/3.08         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 2.89/3.08          | ~ (v1_funct_1 @ X6)
% 2.89/3.08          | ~ (v1_relat_1 @ X6))),
% 2.89/3.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.89/3.08  thf('66', plain,
% 2.89/3.08      (![X6 : $i]:
% 2.89/3.08         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 2.89/3.08          | ~ (v1_funct_1 @ X6)
% 2.89/3.08          | ~ (v1_relat_1 @ X6))),
% 2.89/3.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.89/3.08  thf('67', plain,
% 2.89/3.08      (![X7 : $i]:
% 2.89/3.08         (~ (v2_funct_1 @ X7)
% 2.89/3.08          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 2.89/3.08          | ~ (v1_funct_1 @ X7)
% 2.89/3.08          | ~ (v1_relat_1 @ X7))),
% 2.89/3.08      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.89/3.08  thf(t3_funct_2, axiom,
% 2.89/3.08    (![A:$i]:
% 2.89/3.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.89/3.08       ( ( v1_funct_1 @ A ) & 
% 2.89/3.08         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.89/3.08         ( m1_subset_1 @
% 2.89/3.08           A @ 
% 2.89/3.08           ( k1_zfmisc_1 @
% 2.89/3.08             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.89/3.08  thf('68', plain,
% 2.89/3.08      (![X26 : $i]:
% 2.89/3.08         ((v1_funct_2 @ X26 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26))
% 2.89/3.08          | ~ (v1_funct_1 @ X26)
% 2.89/3.08          | ~ (v1_relat_1 @ X26))),
% 2.89/3.08      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.89/3.08  thf('69', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.89/3.08           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.89/3.08          | ~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.89/3.08          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.89/3.08      inference('sup+', [status(thm)], ['67', '68'])).
% 2.89/3.08  thf('70', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         (~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0)
% 2.89/3.08          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.89/3.08             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.89/3.08      inference('sup-', [status(thm)], ['66', '69'])).
% 2.89/3.08  thf('71', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.89/3.08           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0))),
% 2.89/3.08      inference('simplify', [status(thm)], ['70'])).
% 2.89/3.08  thf('72', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         (~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.89/3.08             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.89/3.08      inference('sup-', [status(thm)], ['65', '71'])).
% 2.89/3.08  thf('73', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.89/3.08           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0))),
% 2.89/3.08      inference('simplify', [status(thm)], ['72'])).
% 2.89/3.08  thf('74', plain,
% 2.89/3.08      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 2.89/3.08         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.89/3.08        | ~ (v1_relat_1 @ sk_C)
% 2.89/3.08        | ~ (v1_funct_1 @ sk_C)
% 2.89/3.08        | ~ (v2_funct_1 @ sk_C))),
% 2.89/3.08      inference('sup+', [status(thm)], ['64', '73'])).
% 2.89/3.08  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 2.89/3.08      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.08  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('78', plain,
% 2.89/3.08      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 2.89/3.08        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.89/3.08      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 2.89/3.08  thf('79', plain,
% 2.89/3.08      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 2.89/3.08        | ~ (v1_relat_1 @ sk_C)
% 2.89/3.08        | ~ (v1_funct_1 @ sk_C)
% 2.89/3.08        | ~ (v2_funct_1 @ sk_C))),
% 2.89/3.08      inference('sup+', [status(thm)], ['63', '78'])).
% 2.89/3.08  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 2.89/3.08      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.08  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('83', plain,
% 2.89/3.08      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 2.89/3.08      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 2.89/3.08  thf('84', plain,
% 2.89/3.08      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.89/3.08         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.89/3.08      inference('sup+', [status(thm)], ['62', '83'])).
% 2.89/3.08  thf('85', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.89/3.08      inference('demod', [status(thm)], ['11', '84'])).
% 2.89/3.08  thf('86', plain,
% 2.89/3.08      (~
% 2.89/3.08       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 2.89/3.08       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 2.89/3.08       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.89/3.08      inference('split', [status(esa)], ['0'])).
% 2.89/3.08  thf('87', plain,
% 2.89/3.08      (~
% 2.89/3.08       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.89/3.08      inference('sat_resolution*', [status(thm)], ['10', '85', '86'])).
% 2.89/3.08  thf('88', plain,
% 2.89/3.08      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.89/3.08      inference('simpl_trail', [status(thm)], ['1', '87'])).
% 2.89/3.08  thf('89', plain,
% 2.89/3.08      (![X7 : $i]:
% 2.89/3.08         (~ (v2_funct_1 @ X7)
% 2.89/3.08          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 2.89/3.08          | ~ (v1_funct_1 @ X7)
% 2.89/3.08          | ~ (v1_relat_1 @ X7))),
% 2.89/3.08      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.89/3.08  thf('90', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.89/3.08      inference('sup+', [status(thm)], ['14', '15'])).
% 2.89/3.08  thf('91', plain,
% 2.89/3.08      (![X6 : $i]:
% 2.89/3.08         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 2.89/3.08          | ~ (v1_funct_1 @ X6)
% 2.89/3.08          | ~ (v1_relat_1 @ X6))),
% 2.89/3.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.89/3.08  thf('92', plain,
% 2.89/3.08      (![X6 : $i]:
% 2.89/3.08         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 2.89/3.08          | ~ (v1_funct_1 @ X6)
% 2.89/3.08          | ~ (v1_relat_1 @ X6))),
% 2.89/3.08      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.89/3.08  thf('93', plain,
% 2.89/3.08      (![X7 : $i]:
% 2.89/3.08         (~ (v2_funct_1 @ X7)
% 2.89/3.08          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 2.89/3.08          | ~ (v1_funct_1 @ X7)
% 2.89/3.08          | ~ (v1_relat_1 @ X7))),
% 2.89/3.08      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.89/3.08  thf('94', plain,
% 2.89/3.08      (![X26 : $i]:
% 2.89/3.08         ((m1_subset_1 @ X26 @ 
% 2.89/3.08           (k1_zfmisc_1 @ 
% 2.89/3.08            (k2_zfmisc_1 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26))))
% 2.89/3.08          | ~ (v1_funct_1 @ X26)
% 2.89/3.08          | ~ (v1_relat_1 @ X26))),
% 2.89/3.08      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.89/3.08  thf('95', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.89/3.08           (k1_zfmisc_1 @ 
% 2.89/3.08            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.89/3.08          | ~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.89/3.08          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.89/3.08      inference('sup+', [status(thm)], ['93', '94'])).
% 2.89/3.08  thf('96', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         (~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0)
% 2.89/3.08          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.89/3.08             (k1_zfmisc_1 @ 
% 2.89/3.08              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.89/3.08               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.89/3.08      inference('sup-', [status(thm)], ['92', '95'])).
% 2.89/3.08  thf('97', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.89/3.08           (k1_zfmisc_1 @ 
% 2.89/3.08            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0))),
% 2.89/3.08      inference('simplify', [status(thm)], ['96'])).
% 2.89/3.08  thf('98', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         (~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.89/3.08             (k1_zfmisc_1 @ 
% 2.89/3.08              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.89/3.08               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.89/3.08      inference('sup-', [status(thm)], ['91', '97'])).
% 2.89/3.08  thf('99', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.89/3.08           (k1_zfmisc_1 @ 
% 2.89/3.08            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.89/3.08          | ~ (v2_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_funct_1 @ X0)
% 2.89/3.08          | ~ (v1_relat_1 @ X0))),
% 2.89/3.08      inference('simplify', [status(thm)], ['98'])).
% 2.89/3.08  thf('100', plain,
% 2.89/3.08      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08         (k1_zfmisc_1 @ 
% 2.89/3.08          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.89/3.08        | ~ (v1_relat_1 @ sk_C)
% 2.89/3.08        | ~ (v1_funct_1 @ sk_C)
% 2.89/3.08        | ~ (v2_funct_1 @ sk_C))),
% 2.89/3.08      inference('sup+', [status(thm)], ['90', '99'])).
% 2.89/3.08  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 2.89/3.08      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.08  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('104', plain,
% 2.89/3.08      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08        (k1_zfmisc_1 @ 
% 2.89/3.08         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.89/3.08      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 2.89/3.08  thf('105', plain,
% 2.89/3.08      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 2.89/3.08        | ~ (v1_relat_1 @ sk_C)
% 2.89/3.08        | ~ (v1_funct_1 @ sk_C)
% 2.89/3.08        | ~ (v2_funct_1 @ sk_C))),
% 2.89/3.08      inference('sup+', [status(thm)], ['89', '104'])).
% 2.89/3.08  thf('106', plain,
% 2.89/3.08      (![X0 : $i]:
% 2.89/3.08         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 2.89/3.08      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.89/3.08  thf('107', plain,
% 2.89/3.08      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.89/3.08         <= (~
% 2.89/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.89/3.08      inference('split', [status(esa)], ['0'])).
% 2.89/3.08  thf('108', plain,
% 2.89/3.08      ((![X0 : $i]:
% 2.89/3.08          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 2.89/3.08              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.89/3.08           | (zip_tseitin_0 @ sk_B @ X0)))
% 2.89/3.08         <= (~
% 2.89/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.89/3.08      inference('sup-', [status(thm)], ['106', '107'])).
% 2.89/3.08  thf('109', plain,
% 2.89/3.08      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 2.89/3.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.89/3.08  thf('110', plain,
% 2.89/3.08      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 2.89/3.08         <= (~
% 2.89/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.89/3.08      inference('demod', [status(thm)], ['108', '109'])).
% 2.89/3.08  thf('111', plain,
% 2.89/3.08      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.89/3.08      inference('sup-', [status(thm)], ['51', '52'])).
% 2.89/3.08  thf('112', plain,
% 2.89/3.08      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 2.89/3.08         <= (~
% 2.89/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.89/3.08      inference('sup-', [status(thm)], ['110', '111'])).
% 2.89/3.08  thf('113', plain,
% 2.89/3.08      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.89/3.08      inference('demod', [status(thm)], ['57', '60'])).
% 2.89/3.08  thf('114', plain,
% 2.89/3.08      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.89/3.08         <= (~
% 2.89/3.08             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.89/3.08      inference('sup-', [status(thm)], ['112', '113'])).
% 2.89/3.08  thf('115', plain,
% 2.89/3.08      (~
% 2.89/3.08       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.89/3.08      inference('sat_resolution*', [status(thm)], ['10', '85', '86'])).
% 2.89/3.08  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.89/3.08      inference('simpl_trail', [status(thm)], ['114', '115'])).
% 2.89/3.08  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 2.89/3.08      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.08  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 2.89/3.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.08  thf('120', plain,
% 2.89/3.08      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.89/3.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.89/3.08      inference('demod', [status(thm)], ['105', '116', '117', '118', '119'])).
% 2.89/3.08  thf('121', plain, ($false), inference('demod', [status(thm)], ['88', '120'])).
% 2.89/3.08  
% 2.89/3.08  % SZS output end Refutation
% 2.89/3.08  
% 2.89/3.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
