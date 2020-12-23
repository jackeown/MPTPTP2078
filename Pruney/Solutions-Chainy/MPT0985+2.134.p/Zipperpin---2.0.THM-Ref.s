%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDA2FsuNsQ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:45 EST 2020

% Result     : Theorem 6.15s
% Output     : Refutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 530 expanded)
%              Number of leaves         :   38 ( 168 expanded)
%              Depth                    :   25
%              Number of atoms          : 1497 (8175 expanded)
%              Number of equality atoms :   72 ( 333 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('64',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('65',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('66',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X5 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( v1_funct_2 @ X29 @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','87','88'])).

thf('90',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','89'])).

thf('91',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('95',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('96',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('98',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X5 @ X6 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('100',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('102',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('115',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('117',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('119',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','87','88'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['110','121'])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['91','130'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('133',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['90','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDA2FsuNsQ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.15/6.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.15/6.39  % Solved by: fo/fo7.sh
% 6.15/6.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.15/6.39  % done 4680 iterations in 5.948s
% 6.15/6.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.15/6.39  % SZS output start Refutation
% 6.15/6.39  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.15/6.39  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.15/6.39  thf(sk_B_type, type, sk_B: $i).
% 6.15/6.39  thf(sk_C_type, type, sk_C: $i).
% 6.15/6.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.15/6.39  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.15/6.39  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.15/6.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.15/6.39  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.15/6.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.15/6.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.15/6.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.15/6.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.15/6.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.15/6.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.15/6.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.15/6.39  thf(sk_A_type, type, sk_A: $i).
% 6.15/6.39  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.15/6.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.15/6.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.15/6.39  thf(t31_funct_2, conjecture,
% 6.15/6.39    (![A:$i,B:$i,C:$i]:
% 6.15/6.39     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.15/6.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.15/6.39       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.15/6.39         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.15/6.39           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.15/6.39           ( m1_subset_1 @
% 6.15/6.39             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 6.15/6.39  thf(zf_stmt_0, negated_conjecture,
% 6.15/6.39    (~( ![A:$i,B:$i,C:$i]:
% 6.15/6.39        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.15/6.39            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.15/6.39          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.15/6.39            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.15/6.39              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.15/6.39              ( m1_subset_1 @
% 6.15/6.39                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 6.15/6.39    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 6.15/6.39  thf('0', plain,
% 6.15/6.39      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.15/6.39        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 6.15/6.39        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.39  thf('1', plain,
% 6.15/6.39      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.39           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 6.15/6.39         <= (~
% 6.15/6.39             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.39               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.15/6.39      inference('split', [status(esa)], ['0'])).
% 6.15/6.39  thf('2', plain,
% 6.15/6.39      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.39  thf(cc1_relset_1, axiom,
% 6.15/6.39    (![A:$i,B:$i,C:$i]:
% 6.15/6.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.15/6.39       ( v1_relat_1 @ C ) ))).
% 6.15/6.39  thf('3', plain,
% 6.15/6.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.15/6.39         ((v1_relat_1 @ X12)
% 6.15/6.39          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 6.15/6.39      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.15/6.39  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.39      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.39  thf(dt_k2_funct_1, axiom,
% 6.15/6.39    (![A:$i]:
% 6.15/6.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.15/6.39       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.15/6.39         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.15/6.39  thf('5', plain,
% 6.15/6.39      (![X9 : $i]:
% 6.15/6.39         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.15/6.39          | ~ (v1_funct_1 @ X9)
% 6.15/6.39          | ~ (v1_relat_1 @ X9))),
% 6.15/6.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.15/6.39  thf('6', plain,
% 6.15/6.39      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.15/6.39         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.15/6.39      inference('split', [status(esa)], ['0'])).
% 6.15/6.39  thf('7', plain,
% 6.15/6.39      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 6.15/6.39         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.15/6.39      inference('sup-', [status(thm)], ['5', '6'])).
% 6.15/6.39  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.39  thf('9', plain,
% 6.15/6.39      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.15/6.39      inference('demod', [status(thm)], ['7', '8'])).
% 6.15/6.39  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.15/6.39      inference('sup-', [status(thm)], ['4', '9'])).
% 6.15/6.39  thf('11', plain,
% 6.15/6.39      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 6.15/6.39         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.39      inference('split', [status(esa)], ['0'])).
% 6.15/6.39  thf('12', plain,
% 6.15/6.39      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.39  thf(redefinition_k2_relset_1, axiom,
% 6.15/6.39    (![A:$i,B:$i,C:$i]:
% 6.15/6.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.15/6.39       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.15/6.39  thf('13', plain,
% 6.15/6.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.15/6.39         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 6.15/6.39          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 6.15/6.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.15/6.39  thf('14', plain,
% 6.15/6.39      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.15/6.39      inference('sup-', [status(thm)], ['12', '13'])).
% 6.15/6.39  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.39  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.15/6.39      inference('sup+', [status(thm)], ['14', '15'])).
% 6.15/6.39  thf(d1_funct_2, axiom,
% 6.15/6.39    (![A:$i,B:$i,C:$i]:
% 6.15/6.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.15/6.39       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.15/6.39           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.15/6.39             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.15/6.39         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.15/6.39           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.15/6.39             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.15/6.39  thf(zf_stmt_1, axiom,
% 6.15/6.39    (![B:$i,A:$i]:
% 6.15/6.39     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.15/6.39       ( zip_tseitin_0 @ B @ A ) ))).
% 6.15/6.39  thf('17', plain,
% 6.15/6.39      (![X21 : $i, X22 : $i]:
% 6.15/6.39         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.15/6.39  thf('18', plain,
% 6.15/6.39      (![X9 : $i]:
% 6.15/6.39         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.15/6.39          | ~ (v1_funct_1 @ X9)
% 6.15/6.39          | ~ (v1_relat_1 @ X9))),
% 6.15/6.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.15/6.39  thf(t55_funct_1, axiom,
% 6.15/6.39    (![A:$i]:
% 6.15/6.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.15/6.39       ( ( v2_funct_1 @ A ) =>
% 6.15/6.39         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.15/6.39           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.15/6.39  thf('19', plain,
% 6.15/6.39      (![X10 : $i]:
% 6.15/6.39         (~ (v2_funct_1 @ X10)
% 6.15/6.39          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 6.15/6.39          | ~ (v1_funct_1 @ X10)
% 6.15/6.39          | ~ (v1_relat_1 @ X10))),
% 6.15/6.39      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.15/6.39  thf(t64_relat_1, axiom,
% 6.15/6.39    (![A:$i]:
% 6.15/6.39     ( ( v1_relat_1 @ A ) =>
% 6.15/6.39       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 6.15/6.39           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 6.15/6.39         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 6.15/6.39  thf('20', plain,
% 6.15/6.39      (![X8 : $i]:
% 6.15/6.39         (((k1_relat_1 @ X8) != (k1_xboole_0))
% 6.15/6.39          | ((X8) = (k1_xboole_0))
% 6.15/6.39          | ~ (v1_relat_1 @ X8))),
% 6.15/6.39      inference('cnf', [status(esa)], [t64_relat_1])).
% 6.15/6.39  thf('21', plain,
% 6.15/6.39      (![X0 : $i]:
% 6.15/6.39         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 6.15/6.39          | ~ (v1_relat_1 @ X0)
% 6.15/6.39          | ~ (v1_funct_1 @ X0)
% 6.15/6.39          | ~ (v2_funct_1 @ X0)
% 6.15/6.39          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.15/6.39          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 6.15/6.39      inference('sup-', [status(thm)], ['19', '20'])).
% 6.15/6.39  thf('22', plain,
% 6.15/6.39      (![X0 : $i]:
% 6.15/6.39         (~ (v1_relat_1 @ X0)
% 6.15/6.39          | ~ (v1_funct_1 @ X0)
% 6.15/6.39          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 6.15/6.39          | ~ (v2_funct_1 @ X0)
% 6.15/6.39          | ~ (v1_funct_1 @ X0)
% 6.15/6.39          | ~ (v1_relat_1 @ X0)
% 6.15/6.39          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 6.15/6.39      inference('sup-', [status(thm)], ['18', '21'])).
% 6.15/6.39  thf('23', plain,
% 6.15/6.39      (![X0 : $i]:
% 6.15/6.39         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 6.15/6.39          | ~ (v2_funct_1 @ X0)
% 6.15/6.39          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 6.15/6.39          | ~ (v1_funct_1 @ X0)
% 6.15/6.39          | ~ (v1_relat_1 @ X0))),
% 6.15/6.39      inference('simplify', [status(thm)], ['22'])).
% 6.15/6.39  thf('24', plain,
% 6.15/6.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.15/6.39         (((k2_relat_1 @ X1) != (X0))
% 6.15/6.39          | (zip_tseitin_0 @ X0 @ X2)
% 6.15/6.39          | ~ (v1_relat_1 @ X1)
% 6.15/6.39          | ~ (v1_funct_1 @ X1)
% 6.15/6.39          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 6.15/6.39          | ~ (v2_funct_1 @ X1))),
% 6.15/6.39      inference('sup-', [status(thm)], ['17', '23'])).
% 6.15/6.39  thf('25', plain,
% 6.15/6.39      (![X1 : $i, X2 : $i]:
% 6.15/6.39         (~ (v2_funct_1 @ X1)
% 6.15/6.39          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 6.15/6.39          | ~ (v1_funct_1 @ X1)
% 6.15/6.39          | ~ (v1_relat_1 @ X1)
% 6.15/6.39          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 6.15/6.39      inference('simplify', [status(thm)], ['24'])).
% 6.15/6.39  thf('26', plain,
% 6.15/6.39      (![X0 : $i]:
% 6.15/6.39         ((zip_tseitin_0 @ sk_B @ X0)
% 6.15/6.39          | ~ (v1_relat_1 @ sk_C)
% 6.15/6.39          | ~ (v1_funct_1 @ sk_C)
% 6.15/6.39          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 6.15/6.39          | ~ (v2_funct_1 @ sk_C))),
% 6.15/6.39      inference('sup+', [status(thm)], ['16', '25'])).
% 6.15/6.39  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.39      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.39  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.39  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 6.15/6.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.39  thf('30', plain,
% 6.15/6.39      (![X0 : $i]:
% 6.15/6.39         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 6.15/6.39      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 6.15/6.39  thf('31', plain,
% 6.15/6.39      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 6.15/6.39         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.39      inference('split', [status(esa)], ['0'])).
% 6.15/6.39  thf('32', plain,
% 6.15/6.39      ((![X0 : $i]:
% 6.15/6.39          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 6.15/6.39           | (zip_tseitin_0 @ sk_B @ X0)))
% 6.15/6.39         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.39      inference('sup-', [status(thm)], ['30', '31'])).
% 6.15/6.40  thf('33', plain,
% 6.15/6.40      (![X21 : $i, X22 : $i]:
% 6.15/6.40         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.15/6.40  thf(t4_subset_1, axiom,
% 6.15/6.40    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.15/6.40  thf('34', plain,
% 6.15/6.40      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 6.15/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.15/6.40  thf(redefinition_k1_relset_1, axiom,
% 6.15/6.40    (![A:$i,B:$i,C:$i]:
% 6.15/6.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.15/6.40       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.15/6.40  thf('35', plain,
% 6.15/6.40      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.15/6.40         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 6.15/6.40          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 6.15/6.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.15/6.40  thf('36', plain,
% 6.15/6.40      (![X0 : $i, X1 : $i]:
% 6.15/6.40         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 6.15/6.40      inference('sup-', [status(thm)], ['34', '35'])).
% 6.15/6.40  thf(t60_relat_1, axiom,
% 6.15/6.40    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 6.15/6.40     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.15/6.40  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.15/6.40      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.15/6.40  thf('38', plain,
% 6.15/6.40      (![X0 : $i, X1 : $i]:
% 6.15/6.40         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.15/6.40      inference('demod', [status(thm)], ['36', '37'])).
% 6.15/6.40  thf(zf_stmt_2, axiom,
% 6.15/6.40    (![C:$i,B:$i,A:$i]:
% 6.15/6.40     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.15/6.40       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.15/6.40  thf('39', plain,
% 6.15/6.40      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.15/6.40         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 6.15/6.40          | (v1_funct_2 @ X25 @ X23 @ X24)
% 6.15/6.40          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.15/6.40  thf('40', plain,
% 6.15/6.40      (![X0 : $i, X1 : $i]:
% 6.15/6.40         (((X1) != (k1_xboole_0))
% 6.15/6.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 6.15/6.40          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 6.15/6.40      inference('sup-', [status(thm)], ['38', '39'])).
% 6.15/6.40  thf('41', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 6.15/6.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 6.15/6.40      inference('simplify', [status(thm)], ['40'])).
% 6.15/6.40  thf('42', plain,
% 6.15/6.40      (![X21 : $i, X22 : $i]:
% 6.15/6.40         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.15/6.40  thf('43', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 6.15/6.40      inference('simplify', [status(thm)], ['42'])).
% 6.15/6.40  thf('44', plain,
% 6.15/6.40      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 6.15/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.15/6.40  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.15/6.40  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.15/6.40  thf(zf_stmt_5, axiom,
% 6.15/6.40    (![A:$i,B:$i,C:$i]:
% 6.15/6.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.15/6.40       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.15/6.40         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.15/6.40           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.15/6.40             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.15/6.40  thf('45', plain,
% 6.15/6.40      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.15/6.40         (~ (zip_tseitin_0 @ X26 @ X27)
% 6.15/6.40          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 6.15/6.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.15/6.40  thf('46', plain,
% 6.15/6.40      (![X0 : $i, X1 : $i]:
% 6.15/6.40         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 6.15/6.40      inference('sup-', [status(thm)], ['44', '45'])).
% 6.15/6.40  thf('47', plain,
% 6.15/6.40      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 6.15/6.40      inference('sup-', [status(thm)], ['43', '46'])).
% 6.15/6.40  thf('48', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 6.15/6.40      inference('demod', [status(thm)], ['41', '47'])).
% 6.15/6.40  thf('49', plain,
% 6.15/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.15/6.40         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 6.15/6.40      inference('sup+', [status(thm)], ['33', '48'])).
% 6.15/6.40  thf('50', plain,
% 6.15/6.40      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 6.15/6.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.40      inference('clc', [status(thm)], ['32', '49'])).
% 6.15/6.40  thf('51', plain,
% 6.15/6.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('52', plain,
% 6.15/6.40      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.15/6.40         (~ (zip_tseitin_0 @ X26 @ X27)
% 6.15/6.40          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 6.15/6.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.15/6.40  thf('53', plain,
% 6.15/6.40      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.15/6.40      inference('sup-', [status(thm)], ['51', '52'])).
% 6.15/6.40  thf('54', plain,
% 6.15/6.40      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 6.15/6.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.40      inference('sup-', [status(thm)], ['50', '53'])).
% 6.15/6.40  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('56', plain,
% 6.15/6.40      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.15/6.40         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 6.15/6.40          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 6.15/6.40          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.15/6.40  thf('57', plain,
% 6.15/6.40      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 6.15/6.40        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 6.15/6.40      inference('sup-', [status(thm)], ['55', '56'])).
% 6.15/6.40  thf('58', plain,
% 6.15/6.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('59', plain,
% 6.15/6.40      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.15/6.40         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 6.15/6.40          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 6.15/6.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.15/6.40  thf('60', plain,
% 6.15/6.40      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.15/6.40      inference('sup-', [status(thm)], ['58', '59'])).
% 6.15/6.40  thf('61', plain,
% 6.15/6.40      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.15/6.40      inference('demod', [status(thm)], ['57', '60'])).
% 6.15/6.40  thf('62', plain,
% 6.15/6.40      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 6.15/6.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.40      inference('sup-', [status(thm)], ['54', '61'])).
% 6.15/6.40  thf('63', plain,
% 6.15/6.40      (![X10 : $i]:
% 6.15/6.40         (~ (v2_funct_1 @ X10)
% 6.15/6.40          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 6.15/6.40          | ~ (v1_funct_1 @ X10)
% 6.15/6.40          | ~ (v1_relat_1 @ X10))),
% 6.15/6.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.15/6.40  thf('64', plain,
% 6.15/6.40      (![X9 : $i]:
% 6.15/6.40         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.15/6.40          | ~ (v1_funct_1 @ X9)
% 6.15/6.40          | ~ (v1_relat_1 @ X9))),
% 6.15/6.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.15/6.40  thf('65', plain,
% 6.15/6.40      (![X9 : $i]:
% 6.15/6.40         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.15/6.40          | ~ (v1_funct_1 @ X9)
% 6.15/6.40          | ~ (v1_relat_1 @ X9))),
% 6.15/6.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.15/6.40  thf(t169_relat_1, axiom,
% 6.15/6.40    (![A:$i]:
% 6.15/6.40     ( ( v1_relat_1 @ A ) =>
% 6.15/6.40       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 6.15/6.40  thf('66', plain,
% 6.15/6.40      (![X7 : $i]:
% 6.15/6.40         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 6.15/6.40          | ~ (v1_relat_1 @ X7))),
% 6.15/6.40      inference('cnf', [status(esa)], [t169_relat_1])).
% 6.15/6.40  thf(t167_relat_1, axiom,
% 6.15/6.40    (![A:$i,B:$i]:
% 6.15/6.40     ( ( v1_relat_1 @ B ) =>
% 6.15/6.40       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 6.15/6.40  thf('67', plain,
% 6.15/6.40      (![X5 : $i, X6 : $i]:
% 6.15/6.40         ((r1_tarski @ (k10_relat_1 @ X5 @ X6) @ (k1_relat_1 @ X5))
% 6.15/6.40          | ~ (v1_relat_1 @ X5))),
% 6.15/6.40      inference('cnf', [status(esa)], [t167_relat_1])).
% 6.15/6.40  thf('68', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0))),
% 6.15/6.40      inference('sup+', [status(thm)], ['66', '67'])).
% 6.15/6.40  thf('69', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v1_relat_1 @ X0)
% 6.15/6.40          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 6.15/6.40      inference('simplify', [status(thm)], ['68'])).
% 6.15/6.40  thf('70', plain,
% 6.15/6.40      (![X10 : $i]:
% 6.15/6.40         (~ (v2_funct_1 @ X10)
% 6.15/6.40          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 6.15/6.40          | ~ (v1_funct_1 @ X10)
% 6.15/6.40          | ~ (v1_relat_1 @ X10))),
% 6.15/6.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.15/6.40  thf(t4_funct_2, axiom,
% 6.15/6.40    (![A:$i,B:$i]:
% 6.15/6.40     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.15/6.40       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 6.15/6.40         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 6.15/6.40           ( m1_subset_1 @
% 6.15/6.40             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 6.15/6.40  thf('71', plain,
% 6.15/6.40      (![X29 : $i, X30 : $i]:
% 6.15/6.40         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 6.15/6.40          | (v1_funct_2 @ X29 @ (k1_relat_1 @ X29) @ X30)
% 6.15/6.40          | ~ (v1_funct_1 @ X29)
% 6.15/6.40          | ~ (v1_relat_1 @ X29))),
% 6.15/6.40      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.15/6.40  thf('72', plain,
% 6.15/6.40      (![X0 : $i, X1 : $i]:
% 6.15/6.40         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 6.15/6.40      inference('sup-', [status(thm)], ['70', '71'])).
% 6.15/6.40  thf('73', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v1_relat_1 @ X0)
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | ~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0))),
% 6.15/6.40      inference('sup-', [status(thm)], ['69', '72'])).
% 6.15/6.40  thf('74', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v1_relat_1 @ X0))),
% 6.15/6.40      inference('simplify', [status(thm)], ['73'])).
% 6.15/6.40  thf('75', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | ~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0))),
% 6.15/6.40      inference('sup-', [status(thm)], ['65', '74'])).
% 6.15/6.40  thf('76', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0))),
% 6.15/6.40      inference('simplify', [status(thm)], ['75'])).
% 6.15/6.40  thf('77', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v2_funct_1 @ X0))),
% 6.15/6.40      inference('sup-', [status(thm)], ['64', '76'])).
% 6.15/6.40  thf('78', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v2_funct_1 @ X0)
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0))),
% 6.15/6.40      inference('simplify', [status(thm)], ['77'])).
% 6.15/6.40  thf('79', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.15/6.40           (k1_relat_1 @ X0))
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v2_funct_1 @ X0))),
% 6.15/6.40      inference('sup+', [status(thm)], ['63', '78'])).
% 6.15/6.40  thf('80', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         (~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.15/6.40             (k1_relat_1 @ X0)))),
% 6.15/6.40      inference('simplify', [status(thm)], ['79'])).
% 6.15/6.40  thf('81', plain,
% 6.15/6.40      ((((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 6.15/6.40         | ~ (v1_relat_1 @ sk_C)
% 6.15/6.40         | ~ (v1_funct_1 @ sk_C)
% 6.15/6.40         | ~ (v2_funct_1 @ sk_C)))
% 6.15/6.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.40      inference('sup+', [status(thm)], ['62', '80'])).
% 6.15/6.40  thf('82', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.15/6.40      inference('sup+', [status(thm)], ['14', '15'])).
% 6.15/6.40  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.40  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('86', plain,
% 6.15/6.40      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 6.15/6.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.15/6.40      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 6.15/6.40  thf('87', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 6.15/6.40      inference('demod', [status(thm)], ['11', '86'])).
% 6.15/6.40  thf('88', plain,
% 6.15/6.40      (~
% 6.15/6.40       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 6.15/6.40       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 6.15/6.40       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.15/6.40      inference('split', [status(esa)], ['0'])).
% 6.15/6.40  thf('89', plain,
% 6.15/6.40      (~
% 6.15/6.40       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.15/6.40      inference('sat_resolution*', [status(thm)], ['10', '87', '88'])).
% 6.15/6.40  thf('90', plain,
% 6.15/6.40      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.15/6.40      inference('simpl_trail', [status(thm)], ['1', '89'])).
% 6.15/6.40  thf('91', plain,
% 6.15/6.40      (![X10 : $i]:
% 6.15/6.40         (~ (v2_funct_1 @ X10)
% 6.15/6.40          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 6.15/6.40          | ~ (v1_funct_1 @ X10)
% 6.15/6.40          | ~ (v1_relat_1 @ X10))),
% 6.15/6.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.15/6.40  thf('92', plain,
% 6.15/6.40      (![X9 : $i]:
% 6.15/6.40         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.15/6.40          | ~ (v1_funct_1 @ X9)
% 6.15/6.40          | ~ (v1_relat_1 @ X9))),
% 6.15/6.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.15/6.40  thf('93', plain,
% 6.15/6.40      (![X9 : $i]:
% 6.15/6.40         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.15/6.40          | ~ (v1_funct_1 @ X9)
% 6.15/6.40          | ~ (v1_relat_1 @ X9))),
% 6.15/6.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.15/6.40  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.15/6.40      inference('sup+', [status(thm)], ['14', '15'])).
% 6.15/6.40  thf('95', plain,
% 6.15/6.40      (![X7 : $i]:
% 6.15/6.40         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 6.15/6.40          | ~ (v1_relat_1 @ X7))),
% 6.15/6.40      inference('cnf', [status(esa)], [t169_relat_1])).
% 6.15/6.40  thf('96', plain,
% 6.15/6.40      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 6.15/6.40        | ~ (v1_relat_1 @ sk_C))),
% 6.15/6.40      inference('sup+', [status(thm)], ['94', '95'])).
% 6.15/6.40  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.40  thf('98', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 6.15/6.40      inference('demod', [status(thm)], ['96', '97'])).
% 6.15/6.40  thf('99', plain,
% 6.15/6.40      (![X5 : $i, X6 : $i]:
% 6.15/6.40         ((r1_tarski @ (k10_relat_1 @ X5 @ X6) @ (k1_relat_1 @ X5))
% 6.15/6.40          | ~ (v1_relat_1 @ X5))),
% 6.15/6.40      inference('cnf', [status(esa)], [t167_relat_1])).
% 6.15/6.40  thf('100', plain,
% 6.15/6.40      (((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 6.15/6.40        | ~ (v1_relat_1 @ sk_C))),
% 6.15/6.40      inference('sup+', [status(thm)], ['98', '99'])).
% 6.15/6.40  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.40  thf('102', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 6.15/6.40      inference('demod', [status(thm)], ['100', '101'])).
% 6.15/6.40  thf('103', plain,
% 6.15/6.40      (![X10 : $i]:
% 6.15/6.40         (~ (v2_funct_1 @ X10)
% 6.15/6.40          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 6.15/6.40          | ~ (v1_funct_1 @ X10)
% 6.15/6.40          | ~ (v1_relat_1 @ X10))),
% 6.15/6.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.15/6.40  thf('104', plain,
% 6.15/6.40      (![X29 : $i, X30 : $i]:
% 6.15/6.40         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 6.15/6.40          | (m1_subset_1 @ X29 @ 
% 6.15/6.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ X30)))
% 6.15/6.40          | ~ (v1_funct_1 @ X29)
% 6.15/6.40          | ~ (v1_relat_1 @ X29))),
% 6.15/6.40      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.15/6.40  thf('105', plain,
% 6.15/6.40      (![X0 : $i, X1 : $i]:
% 6.15/6.40         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 6.15/6.40          | ~ (v1_relat_1 @ X0)
% 6.15/6.40          | ~ (v1_funct_1 @ X0)
% 6.15/6.40          | ~ (v2_funct_1 @ X0)
% 6.15/6.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.15/6.40          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.15/6.40             (k1_zfmisc_1 @ 
% 6.15/6.40              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 6.15/6.40      inference('sup-', [status(thm)], ['103', '104'])).
% 6.15/6.40  thf('106', plain,
% 6.15/6.40      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40         (k1_zfmisc_1 @ 
% 6.15/6.40          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.15/6.40           (k1_relat_1 @ sk_C))))
% 6.15/6.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.15/6.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.15/6.40        | ~ (v2_funct_1 @ sk_C)
% 6.15/6.40        | ~ (v1_funct_1 @ sk_C)
% 6.15/6.40        | ~ (v1_relat_1 @ sk_C))),
% 6.15/6.40      inference('sup-', [status(thm)], ['102', '105'])).
% 6.15/6.40  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.40  thf('110', plain,
% 6.15/6.40      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40         (k1_zfmisc_1 @ 
% 6.15/6.40          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.15/6.40           (k1_relat_1 @ sk_C))))
% 6.15/6.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.15/6.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.15/6.40      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 6.15/6.40  thf('111', plain,
% 6.15/6.40      (![X0 : $i]:
% 6.15/6.40         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 6.15/6.40      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 6.15/6.40  thf('112', plain,
% 6.15/6.40      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 6.15/6.40         <= (~
% 6.15/6.40             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.15/6.40      inference('split', [status(esa)], ['0'])).
% 6.15/6.40  thf('113', plain,
% 6.15/6.40      ((![X0 : $i]:
% 6.15/6.40          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 6.15/6.40              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 6.15/6.40           | (zip_tseitin_0 @ sk_B @ X0)))
% 6.15/6.40         <= (~
% 6.15/6.40             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.15/6.40      inference('sup-', [status(thm)], ['111', '112'])).
% 6.15/6.40  thf('114', plain,
% 6.15/6.40      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 6.15/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.15/6.40  thf('115', plain,
% 6.15/6.40      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 6.15/6.40         <= (~
% 6.15/6.40             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.15/6.40      inference('demod', [status(thm)], ['113', '114'])).
% 6.15/6.40  thf('116', plain,
% 6.15/6.40      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.15/6.40      inference('sup-', [status(thm)], ['51', '52'])).
% 6.15/6.40  thf('117', plain,
% 6.15/6.40      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 6.15/6.40         <= (~
% 6.15/6.40             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.15/6.40      inference('sup-', [status(thm)], ['115', '116'])).
% 6.15/6.40  thf('118', plain,
% 6.15/6.40      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.15/6.40      inference('demod', [status(thm)], ['57', '60'])).
% 6.15/6.40  thf('119', plain,
% 6.15/6.40      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 6.15/6.40         <= (~
% 6.15/6.40             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.15/6.40      inference('sup-', [status(thm)], ['117', '118'])).
% 6.15/6.40  thf('120', plain,
% 6.15/6.40      (~
% 6.15/6.40       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.15/6.40      inference('sat_resolution*', [status(thm)], ['10', '87', '88'])).
% 6.15/6.40  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 6.15/6.40      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 6.15/6.40  thf('122', plain,
% 6.15/6.40      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40         (k1_zfmisc_1 @ 
% 6.15/6.40          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 6.15/6.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.15/6.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.15/6.40      inference('demod', [status(thm)], ['110', '121'])).
% 6.15/6.40  thf('123', plain,
% 6.15/6.40      ((~ (v1_relat_1 @ sk_C)
% 6.15/6.40        | ~ (v1_funct_1 @ sk_C)
% 6.15/6.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.15/6.40        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40           (k1_zfmisc_1 @ 
% 6.15/6.40            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 6.15/6.40      inference('sup-', [status(thm)], ['93', '122'])).
% 6.15/6.40  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.40  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('126', plain,
% 6.15/6.40      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.15/6.40        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40           (k1_zfmisc_1 @ 
% 6.15/6.40            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 6.15/6.40      inference('demod', [status(thm)], ['123', '124', '125'])).
% 6.15/6.40  thf('127', plain,
% 6.15/6.40      ((~ (v1_relat_1 @ sk_C)
% 6.15/6.40        | ~ (v1_funct_1 @ sk_C)
% 6.15/6.40        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40           (k1_zfmisc_1 @ 
% 6.15/6.40            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 6.15/6.40      inference('sup-', [status(thm)], ['92', '126'])).
% 6.15/6.40  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.40  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('130', plain,
% 6.15/6.40      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40        (k1_zfmisc_1 @ 
% 6.15/6.40         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 6.15/6.40      inference('demod', [status(thm)], ['127', '128', '129'])).
% 6.15/6.40  thf('131', plain,
% 6.15/6.40      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 6.15/6.40        | ~ (v1_relat_1 @ sk_C)
% 6.15/6.40        | ~ (v1_funct_1 @ sk_C)
% 6.15/6.40        | ~ (v2_funct_1 @ sk_C))),
% 6.15/6.40      inference('sup+', [status(thm)], ['91', '130'])).
% 6.15/6.40  thf('132', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.15/6.40      inference('sup+', [status(thm)], ['14', '15'])).
% 6.15/6.40  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 6.15/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.15/6.40  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 6.15/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.15/6.40  thf('136', plain,
% 6.15/6.40      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.15/6.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.15/6.40      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 6.15/6.40  thf('137', plain, ($false), inference('demod', [status(thm)], ['90', '136'])).
% 6.15/6.40  
% 6.15/6.40  % SZS output end Refutation
% 6.15/6.40  
% 6.15/6.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
