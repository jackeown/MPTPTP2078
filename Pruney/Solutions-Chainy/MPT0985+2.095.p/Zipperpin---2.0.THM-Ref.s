%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HjZY19mMON

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:40 EST 2020

% Result     : Theorem 3.15s
% Output     : Refutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 505 expanded)
%              Number of leaves         :   38 ( 162 expanded)
%              Depth                    :   27
%              Number of atoms          : 1408 (7707 expanded)
%              Number of equality atoms :   66 ( 312 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C_1 )
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A_1 )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(clc,[status(thm)],['32','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,
    ( ( sk_A_1
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['62','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('83',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['11','85'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','86','87'])).

thf('89',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','88'])).

thf('90',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('92',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('100',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('102',plain,
    ( ( sk_A_1
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','86','87'])).

thf('104',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('106',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ X32 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('115',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ sk_A_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('119',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['91','120'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['90','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('124',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('125',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['89','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HjZY19mMON
% 0.14/0.37  % Computer   : n002.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:27:52 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 3.15/3.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.15/3.40  % Solved by: fo/fo7.sh
% 3.15/3.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.15/3.40  % done 2912 iterations in 2.949s
% 3.15/3.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.15/3.40  % SZS output start Refutation
% 3.15/3.40  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.15/3.40  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.15/3.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.15/3.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.15/3.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.15/3.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.15/3.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.15/3.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.15/3.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.15/3.40  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.15/3.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.15/3.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.15/3.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.15/3.40  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.15/3.40  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.15/3.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.15/3.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.15/3.40  thf(sk_A_1_type, type, sk_A_1: $i).
% 3.15/3.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.15/3.40  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.15/3.40  thf(sk_B_type, type, sk_B: $i).
% 3.15/3.40  thf(t31_funct_2, conjecture,
% 3.15/3.40    (![A:$i,B:$i,C:$i]:
% 3.15/3.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.15/3.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.15/3.40       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.15/3.40         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.15/3.40           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.15/3.40           ( m1_subset_1 @
% 3.15/3.40             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.15/3.40  thf(zf_stmt_0, negated_conjecture,
% 3.15/3.40    (~( ![A:$i,B:$i,C:$i]:
% 3.15/3.40        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.15/3.40            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.15/3.40          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.15/3.40            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.15/3.40              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.15/3.40              ( m1_subset_1 @
% 3.15/3.40                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 3.15/3.40    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 3.15/3.40  thf('0', plain,
% 3.15/3.40      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 3.15/3.40        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)
% 3.15/3.40        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('1', plain,
% 3.15/3.40      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))
% 3.15/3.40         <= (~
% 3.15/3.40             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.40               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.15/3.40      inference('split', [status(esa)], ['0'])).
% 3.15/3.40  thf('2', plain,
% 3.15/3.40      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf(cc1_relset_1, axiom,
% 3.15/3.40    (![A:$i,B:$i,C:$i]:
% 3.15/3.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.40       ( v1_relat_1 @ C ) ))).
% 3.15/3.40  thf('3', plain,
% 3.15/3.40      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.15/3.40         ((v1_relat_1 @ X14)
% 3.15/3.40          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.15/3.40      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.15/3.40  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.40      inference('sup-', [status(thm)], ['2', '3'])).
% 3.15/3.40  thf(dt_k2_funct_1, axiom,
% 3.15/3.40    (![A:$i]:
% 3.15/3.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.15/3.40       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.15/3.40         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.15/3.40  thf('5', plain,
% 3.15/3.40      (![X12 : $i]:
% 3.15/3.40         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 3.15/3.40          | ~ (v1_funct_1 @ X12)
% 3.15/3.40          | ~ (v1_relat_1 @ X12))),
% 3.15/3.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.15/3.40  thf('6', plain,
% 3.15/3.40      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 3.15/3.40         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 3.15/3.40      inference('split', [status(esa)], ['0'])).
% 3.15/3.40  thf('7', plain,
% 3.15/3.40      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 3.15/3.40         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 3.15/3.40      inference('sup-', [status(thm)], ['5', '6'])).
% 3.15/3.40  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('9', plain,
% 3.15/3.40      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 3.15/3.40      inference('demod', [status(thm)], ['7', '8'])).
% 3.15/3.40  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['4', '9'])).
% 3.15/3.40  thf('11', plain,
% 3.15/3.40      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))
% 3.15/3.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.40      inference('split', [status(esa)], ['0'])).
% 3.15/3.40  thf('12', plain,
% 3.15/3.40      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf(redefinition_k2_relset_1, axiom,
% 3.15/3.40    (![A:$i,B:$i,C:$i]:
% 3.15/3.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.40       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.15/3.40  thf('13', plain,
% 3.15/3.40      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.15/3.40         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 3.15/3.40          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.15/3.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.15/3.40  thf('14', plain,
% 3.15/3.40      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 3.15/3.40      inference('sup-', [status(thm)], ['12', '13'])).
% 3.15/3.40  thf('15', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1) = (sk_B))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('16', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 3.15/3.40      inference('sup+', [status(thm)], ['14', '15'])).
% 3.15/3.40  thf(d1_funct_2, axiom,
% 3.15/3.40    (![A:$i,B:$i,C:$i]:
% 3.15/3.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.40       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.15/3.40           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.15/3.40             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.15/3.40         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.15/3.40           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.15/3.40             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.15/3.40  thf(zf_stmt_1, axiom,
% 3.15/3.40    (![B:$i,A:$i]:
% 3.15/3.40     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.15/3.40       ( zip_tseitin_0 @ B @ A ) ))).
% 3.15/3.40  thf('17', plain,
% 3.15/3.40      (![X23 : $i, X24 : $i]:
% 3.15/3.40         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.15/3.40  thf('18', plain,
% 3.15/3.40      (![X12 : $i]:
% 3.15/3.40         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 3.15/3.40          | ~ (v1_funct_1 @ X12)
% 3.15/3.40          | ~ (v1_relat_1 @ X12))),
% 3.15/3.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.15/3.40  thf(t55_funct_1, axiom,
% 3.15/3.40    (![A:$i]:
% 3.15/3.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.15/3.40       ( ( v2_funct_1 @ A ) =>
% 3.15/3.40         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.15/3.40           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.15/3.40  thf('19', plain,
% 3.15/3.40      (![X13 : $i]:
% 3.15/3.40         (~ (v2_funct_1 @ X13)
% 3.15/3.40          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 3.15/3.40          | ~ (v1_funct_1 @ X13)
% 3.15/3.40          | ~ (v1_relat_1 @ X13))),
% 3.15/3.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.15/3.40  thf(t64_relat_1, axiom,
% 3.15/3.40    (![A:$i]:
% 3.15/3.40     ( ( v1_relat_1 @ A ) =>
% 3.15/3.40       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 3.15/3.40           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.15/3.40         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.15/3.40  thf('20', plain,
% 3.15/3.40      (![X9 : $i]:
% 3.15/3.40         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 3.15/3.40          | ((X9) = (k1_xboole_0))
% 3.15/3.40          | ~ (v1_relat_1 @ X9))),
% 3.15/3.40      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.15/3.40  thf('21', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.15/3.40          | ~ (v1_relat_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ~ (v2_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.15/3.40          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['19', '20'])).
% 3.15/3.40  thf('22', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         (~ (v1_relat_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.15/3.40          | ~ (v2_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ X0)
% 3.15/3.40          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['18', '21'])).
% 3.15/3.40  thf('23', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.15/3.40          | ~ (v2_funct_1 @ X0)
% 3.15/3.40          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ X0))),
% 3.15/3.40      inference('simplify', [status(thm)], ['22'])).
% 3.15/3.40  thf('24', plain,
% 3.15/3.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.15/3.40         (((k2_relat_1 @ X1) != (X0))
% 3.15/3.40          | (zip_tseitin_0 @ X0 @ X2)
% 3.15/3.40          | ~ (v1_relat_1 @ X1)
% 3.15/3.40          | ~ (v1_funct_1 @ X1)
% 3.15/3.40          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.15/3.40          | ~ (v2_funct_1 @ X1))),
% 3.15/3.40      inference('sup-', [status(thm)], ['17', '23'])).
% 3.15/3.40  thf('25', plain,
% 3.15/3.40      (![X1 : $i, X2 : $i]:
% 3.15/3.40         (~ (v2_funct_1 @ X1)
% 3.15/3.40          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.15/3.40          | ~ (v1_funct_1 @ X1)
% 3.15/3.40          | ~ (v1_relat_1 @ X1)
% 3.15/3.40          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 3.15/3.40      inference('simplify', [status(thm)], ['24'])).
% 3.15/3.40  thf('26', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         ((zip_tseitin_0 @ sk_B @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ sk_C_1)
% 3.15/3.40          | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.40          | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0))
% 3.15/3.40          | ~ (v2_funct_1 @ sk_C_1))),
% 3.15/3.40      inference('sup+', [status(thm)], ['16', '25'])).
% 3.15/3.40  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.40      inference('sup-', [status(thm)], ['2', '3'])).
% 3.15/3.40  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('29', plain, ((v2_funct_1 @ sk_C_1)),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('30', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 3.15/3.40      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.15/3.40  thf('31', plain,
% 3.15/3.40      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))
% 3.15/3.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.40      inference('split', [status(esa)], ['0'])).
% 3.15/3.40  thf('32', plain,
% 3.15/3.40      ((![X0 : $i]:
% 3.15/3.40          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A_1)
% 3.15/3.40           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.15/3.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['30', '31'])).
% 3.15/3.40  thf('33', plain,
% 3.15/3.40      (![X23 : $i, X24 : $i]:
% 3.15/3.40         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.15/3.40  thf(t4_subset_1, axiom,
% 3.15/3.40    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.15/3.40  thf('34', plain,
% 3.15/3.40      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 3.15/3.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.15/3.40  thf(redefinition_k1_relset_1, axiom,
% 3.15/3.40    (![A:$i,B:$i,C:$i]:
% 3.15/3.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.40       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.15/3.40  thf('35', plain,
% 3.15/3.40      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.15/3.40         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 3.15/3.40          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.15/3.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.15/3.40  thf('36', plain,
% 3.15/3.40      (![X0 : $i, X1 : $i]:
% 3.15/3.40         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.15/3.40      inference('sup-', [status(thm)], ['34', '35'])).
% 3.15/3.40  thf(t60_relat_1, axiom,
% 3.15/3.40    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.15/3.40     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.15/3.40  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.15/3.40      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.15/3.40  thf('38', plain,
% 3.15/3.40      (![X0 : $i, X1 : $i]:
% 3.15/3.40         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.15/3.40      inference('demod', [status(thm)], ['36', '37'])).
% 3.15/3.40  thf(zf_stmt_2, axiom,
% 3.15/3.40    (![C:$i,B:$i,A:$i]:
% 3.15/3.40     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.15/3.40       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.15/3.40  thf('39', plain,
% 3.15/3.40      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.15/3.40         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 3.15/3.40          | (v1_funct_2 @ X27 @ X25 @ X26)
% 3.15/3.40          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.15/3.40  thf('40', plain,
% 3.15/3.40      (![X0 : $i, X1 : $i]:
% 3.15/3.40         (((X1) != (k1_xboole_0))
% 3.15/3.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.15/3.40          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.15/3.40      inference('sup-', [status(thm)], ['38', '39'])).
% 3.15/3.40  thf('41', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.15/3.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.15/3.40      inference('simplify', [status(thm)], ['40'])).
% 3.15/3.40  thf('42', plain,
% 3.15/3.40      (![X23 : $i, X24 : $i]:
% 3.15/3.40         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.15/3.40  thf('43', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 3.15/3.40      inference('simplify', [status(thm)], ['42'])).
% 3.15/3.40  thf('44', plain,
% 3.15/3.40      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 3.15/3.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.15/3.40  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.15/3.40  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.15/3.40  thf(zf_stmt_5, axiom,
% 3.15/3.40    (![A:$i,B:$i,C:$i]:
% 3.15/3.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.40       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.15/3.40         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.15/3.40           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.15/3.40             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.15/3.40  thf('45', plain,
% 3.15/3.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.15/3.40         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.15/3.40          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.15/3.40          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.15/3.40  thf('46', plain,
% 3.15/3.40      (![X0 : $i, X1 : $i]:
% 3.15/3.40         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.15/3.40      inference('sup-', [status(thm)], ['44', '45'])).
% 3.15/3.40  thf('47', plain,
% 3.15/3.40      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.15/3.40      inference('sup-', [status(thm)], ['43', '46'])).
% 3.15/3.40  thf('48', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.15/3.40      inference('demod', [status(thm)], ['41', '47'])).
% 3.15/3.40  thf('49', plain,
% 3.15/3.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.15/3.40         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.15/3.40      inference('sup+', [status(thm)], ['33', '48'])).
% 3.15/3.40  thf('50', plain,
% 3.15/3.40      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.15/3.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.40      inference('clc', [status(thm)], ['32', '49'])).
% 3.15/3.40  thf('51', plain,
% 3.15/3.40      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('52', plain,
% 3.15/3.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.15/3.40         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.15/3.40          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.15/3.40          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.15/3.40  thf('53', plain,
% 3.15/3.40      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1)
% 3.15/3.40        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 3.15/3.40      inference('sup-', [status(thm)], ['51', '52'])).
% 3.15/3.40  thf('54', plain,
% 3.15/3.40      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1))
% 3.15/3.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['50', '53'])).
% 3.15/3.40  thf('55', plain, ((v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B)),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('56', plain,
% 3.15/3.40      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.15/3.40         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 3.15/3.40          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 3.15/3.40          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.15/3.40  thf('57', plain,
% 3.15/3.40      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1)
% 3.15/3.40        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C_1)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['55', '56'])).
% 3.15/3.40  thf('58', plain,
% 3.15/3.40      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.15/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.40  thf('59', plain,
% 3.15/3.40      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.15/3.40         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 3.15/3.40          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.15/3.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.15/3.40  thf('60', plain,
% 3.15/3.40      (((k1_relset_1 @ sk_A_1 @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.15/3.40      inference('sup-', [status(thm)], ['58', '59'])).
% 3.15/3.40  thf('61', plain,
% 3.15/3.40      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1)
% 3.15/3.40        | ((sk_A_1) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.40      inference('demod', [status(thm)], ['57', '60'])).
% 3.15/3.40  thf('62', plain,
% 3.15/3.40      ((((sk_A_1) = (k1_relat_1 @ sk_C_1)))
% 3.15/3.40         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['54', '61'])).
% 3.15/3.40  thf('63', plain,
% 3.15/3.40      (![X13 : $i]:
% 3.15/3.40         (~ (v2_funct_1 @ X13)
% 3.15/3.40          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 3.15/3.40          | ~ (v1_funct_1 @ X13)
% 3.15/3.40          | ~ (v1_relat_1 @ X13))),
% 3.15/3.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.15/3.40  thf('64', plain,
% 3.15/3.40      (![X12 : $i]:
% 3.15/3.40         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 3.15/3.40          | ~ (v1_funct_1 @ X12)
% 3.15/3.40          | ~ (v1_relat_1 @ X12))),
% 3.15/3.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.15/3.40  thf('65', plain,
% 3.15/3.40      (![X12 : $i]:
% 3.15/3.40         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 3.15/3.40          | ~ (v1_funct_1 @ X12)
% 3.15/3.40          | ~ (v1_relat_1 @ X12))),
% 3.15/3.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.15/3.40  thf('66', plain,
% 3.15/3.40      (![X13 : $i]:
% 3.15/3.40         (~ (v2_funct_1 @ X13)
% 3.15/3.40          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 3.15/3.40          | ~ (v1_funct_1 @ X13)
% 3.15/3.40          | ~ (v1_relat_1 @ X13))),
% 3.15/3.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.15/3.40  thf(d3_tarski, axiom,
% 3.15/3.40    (![A:$i,B:$i]:
% 3.15/3.40     ( ( r1_tarski @ A @ B ) <=>
% 3.15/3.40       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.15/3.40  thf('67', plain,
% 3.15/3.40      (![X1 : $i, X3 : $i]:
% 3.15/3.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.15/3.40      inference('cnf', [status(esa)], [d3_tarski])).
% 3.15/3.40  thf('68', plain,
% 3.15/3.40      (![X1 : $i, X3 : $i]:
% 3.15/3.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.15/3.40      inference('cnf', [status(esa)], [d3_tarski])).
% 3.15/3.40  thf('69', plain,
% 3.15/3.40      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 3.15/3.40      inference('sup-', [status(thm)], ['67', '68'])).
% 3.15/3.40  thf('70', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.15/3.40      inference('simplify', [status(thm)], ['69'])).
% 3.15/3.40  thf(t4_funct_2, axiom,
% 3.15/3.40    (![A:$i,B:$i]:
% 3.15/3.40     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.15/3.40       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.15/3.40         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.15/3.40           ( m1_subset_1 @
% 3.15/3.40             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.15/3.40  thf('71', plain,
% 3.15/3.40      (![X31 : $i, X32 : $i]:
% 3.15/3.40         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 3.15/3.40          | (v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ X32)
% 3.15/3.40          | ~ (v1_funct_1 @ X31)
% 3.15/3.40          | ~ (v1_relat_1 @ X31))),
% 3.15/3.40      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.15/3.40  thf('72', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         (~ (v1_relat_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.15/3.40      inference('sup-', [status(thm)], ['70', '71'])).
% 3.15/3.40  thf('73', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.15/3.40           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.15/3.40          | ~ (v1_relat_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ~ (v2_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.15/3.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.15/3.40      inference('sup+', [status(thm)], ['66', '72'])).
% 3.15/3.40  thf('74', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         (~ (v1_relat_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.15/3.40          | ~ (v2_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ X0)
% 3.15/3.40          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.15/3.40             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.15/3.40      inference('sup-', [status(thm)], ['65', '73'])).
% 3.15/3.40  thf('75', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.15/3.40           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.15/3.40          | ~ (v2_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.40          | ~ (v1_relat_1 @ X0))),
% 3.15/3.40      inference('simplify', [status(thm)], ['74'])).
% 3.15/3.40  thf('76', plain,
% 3.15/3.40      (![X0 : $i]:
% 3.15/3.40         (~ (v1_relat_1 @ X0)
% 3.15/3.40          | ~ (v1_funct_1 @ X0)
% 3.15/3.41          | ~ (v1_relat_1 @ X0)
% 3.15/3.41          | ~ (v1_funct_1 @ X0)
% 3.15/3.41          | ~ (v2_funct_1 @ X0)
% 3.15/3.41          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.15/3.41             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.15/3.41      inference('sup-', [status(thm)], ['64', '75'])).
% 3.15/3.41  thf('77', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.15/3.41           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.15/3.41          | ~ (v2_funct_1 @ X0)
% 3.15/3.41          | ~ (v1_funct_1 @ X0)
% 3.15/3.41          | ~ (v1_relat_1 @ X0))),
% 3.15/3.41      inference('simplify', [status(thm)], ['76'])).
% 3.15/3.41  thf('78', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.15/3.41           (k1_relat_1 @ X0))
% 3.15/3.41          | ~ (v1_relat_1 @ X0)
% 3.15/3.41          | ~ (v1_funct_1 @ X0)
% 3.15/3.41          | ~ (v2_funct_1 @ X0)
% 3.15/3.41          | ~ (v1_relat_1 @ X0)
% 3.15/3.41          | ~ (v1_funct_1 @ X0)
% 3.15/3.41          | ~ (v2_funct_1 @ X0))),
% 3.15/3.41      inference('sup+', [status(thm)], ['63', '77'])).
% 3.15/3.41  thf('79', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         (~ (v2_funct_1 @ X0)
% 3.15/3.41          | ~ (v1_funct_1 @ X0)
% 3.15/3.41          | ~ (v1_relat_1 @ X0)
% 3.15/3.41          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.15/3.41             (k1_relat_1 @ X0)))),
% 3.15/3.41      inference('simplify', [status(thm)], ['78'])).
% 3.15/3.41  thf('80', plain,
% 3.15/3.41      ((((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A_1)
% 3.15/3.41         | ~ (v1_relat_1 @ sk_C_1)
% 3.15/3.41         | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.41         | ~ (v2_funct_1 @ sk_C_1)))
% 3.15/3.41         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.41      inference('sup+', [status(thm)], ['62', '79'])).
% 3.15/3.41  thf('81', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 3.15/3.41      inference('sup+', [status(thm)], ['14', '15'])).
% 3.15/3.41  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.41      inference('sup-', [status(thm)], ['2', '3'])).
% 3.15/3.41  thf('83', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('84', plain, ((v2_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('85', plain,
% 3.15/3.41      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))
% 3.15/3.41         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 3.15/3.41      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 3.15/3.41  thf('86', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))),
% 3.15/3.41      inference('demod', [status(thm)], ['11', '85'])).
% 3.15/3.41  thf('87', plain,
% 3.15/3.41      (~
% 3.15/3.41       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))) | 
% 3.15/3.41       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)) | 
% 3.15/3.41       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 3.15/3.41      inference('split', [status(esa)], ['0'])).
% 3.15/3.41  thf('88', plain,
% 3.15/3.41      (~
% 3.15/3.41       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 3.15/3.41      inference('sat_resolution*', [status(thm)], ['10', '86', '87'])).
% 3.15/3.41  thf('89', plain,
% 3.15/3.41      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.15/3.41      inference('simpl_trail', [status(thm)], ['1', '88'])).
% 3.15/3.41  thf('90', plain,
% 3.15/3.41      (![X13 : $i]:
% 3.15/3.41         (~ (v2_funct_1 @ X13)
% 3.15/3.41          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 3.15/3.41          | ~ (v1_funct_1 @ X13)
% 3.15/3.41          | ~ (v1_relat_1 @ X13))),
% 3.15/3.41      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.15/3.41  thf('91', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.15/3.41      inference('simplify', [status(thm)], ['69'])).
% 3.15/3.41  thf('92', plain,
% 3.15/3.41      (![X12 : $i]:
% 3.15/3.41         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 3.15/3.41          | ~ (v1_funct_1 @ X12)
% 3.15/3.41          | ~ (v1_relat_1 @ X12))),
% 3.15/3.41      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.15/3.41  thf('93', plain,
% 3.15/3.41      (![X12 : $i]:
% 3.15/3.41         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 3.15/3.41          | ~ (v1_funct_1 @ X12)
% 3.15/3.41          | ~ (v1_relat_1 @ X12))),
% 3.15/3.41      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.15/3.41  thf('94', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C_1) = (k1_xboole_0)))),
% 3.15/3.41      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.15/3.41  thf('95', plain,
% 3.15/3.41      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))
% 3.15/3.41         <= (~
% 3.15/3.41             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.15/3.41      inference('split', [status(esa)], ['0'])).
% 3.15/3.41  thf('96', plain,
% 3.15/3.41      ((![X0 : $i]:
% 3.15/3.41          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.15/3.41              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 3.15/3.41           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.15/3.41         <= (~
% 3.15/3.41             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.15/3.41      inference('sup-', [status(thm)], ['94', '95'])).
% 3.15/3.41  thf('97', plain,
% 3.15/3.41      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 3.15/3.41      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.15/3.41  thf('98', plain,
% 3.15/3.41      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.15/3.41         <= (~
% 3.15/3.41             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.15/3.41      inference('demod', [status(thm)], ['96', '97'])).
% 3.15/3.41  thf('99', plain,
% 3.15/3.41      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1)
% 3.15/3.41        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 3.15/3.41      inference('sup-', [status(thm)], ['51', '52'])).
% 3.15/3.41  thf('100', plain,
% 3.15/3.41      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1))
% 3.15/3.41         <= (~
% 3.15/3.41             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.15/3.41      inference('sup-', [status(thm)], ['98', '99'])).
% 3.15/3.41  thf('101', plain,
% 3.15/3.41      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A_1)
% 3.15/3.41        | ((sk_A_1) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.41      inference('demod', [status(thm)], ['57', '60'])).
% 3.15/3.41  thf('102', plain,
% 3.15/3.41      ((((sk_A_1) = (k1_relat_1 @ sk_C_1)))
% 3.15/3.41         <= (~
% 3.15/3.41             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.15/3.41      inference('sup-', [status(thm)], ['100', '101'])).
% 3.15/3.41  thf('103', plain,
% 3.15/3.41      (~
% 3.15/3.41       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 3.15/3.41      inference('sat_resolution*', [status(thm)], ['10', '86', '87'])).
% 3.15/3.41  thf('104', plain, (((sk_A_1) = (k1_relat_1 @ sk_C_1))),
% 3.15/3.41      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 3.15/3.41  thf('105', plain,
% 3.15/3.41      (![X13 : $i]:
% 3.15/3.41         (~ (v2_funct_1 @ X13)
% 3.15/3.41          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 3.15/3.41          | ~ (v1_funct_1 @ X13)
% 3.15/3.41          | ~ (v1_relat_1 @ X13))),
% 3.15/3.41      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.15/3.41  thf('106', plain,
% 3.15/3.41      (![X31 : $i, X32 : $i]:
% 3.15/3.41         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 3.15/3.41          | (m1_subset_1 @ X31 @ 
% 3.15/3.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ X32)))
% 3.15/3.41          | ~ (v1_funct_1 @ X31)
% 3.15/3.41          | ~ (v1_relat_1 @ X31))),
% 3.15/3.41      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.15/3.41  thf('107', plain,
% 3.15/3.41      (![X0 : $i, X1 : $i]:
% 3.15/3.41         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.15/3.41          | ~ (v1_relat_1 @ X0)
% 3.15/3.41          | ~ (v1_funct_1 @ X0)
% 3.15/3.41          | ~ (v2_funct_1 @ X0)
% 3.15/3.41          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.15/3.41          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.15/3.41          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.15/3.41             (k1_zfmisc_1 @ 
% 3.15/3.41              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 3.15/3.41      inference('sup-', [status(thm)], ['105', '106'])).
% 3.15/3.41  thf('108', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         (~ (r1_tarski @ sk_A_1 @ X0)
% 3.15/3.41          | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41             (k1_zfmisc_1 @ 
% 3.15/3.41              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ X0)))
% 3.15/3.41          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 3.15/3.41          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 3.15/3.41          | ~ (v2_funct_1 @ sk_C_1)
% 3.15/3.41          | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.41          | ~ (v1_relat_1 @ sk_C_1))),
% 3.15/3.41      inference('sup-', [status(thm)], ['104', '107'])).
% 3.15/3.41  thf('109', plain, ((v2_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('110', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('111', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.41      inference('sup-', [status(thm)], ['2', '3'])).
% 3.15/3.41  thf('112', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         (~ (r1_tarski @ sk_A_1 @ X0)
% 3.15/3.41          | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41             (k1_zfmisc_1 @ 
% 3.15/3.41              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ X0)))
% 3.15/3.41          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 3.15/3.41          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 3.15/3.41      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 3.15/3.41  thf('113', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         (~ (v1_relat_1 @ sk_C_1)
% 3.15/3.41          | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.41          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 3.15/3.41          | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41             (k1_zfmisc_1 @ 
% 3.15/3.41              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ X0)))
% 3.15/3.41          | ~ (r1_tarski @ sk_A_1 @ X0))),
% 3.15/3.41      inference('sup-', [status(thm)], ['93', '112'])).
% 3.15/3.41  thf('114', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.41      inference('sup-', [status(thm)], ['2', '3'])).
% 3.15/3.41  thf('115', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('116', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         (~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 3.15/3.41          | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41             (k1_zfmisc_1 @ 
% 3.15/3.41              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ X0)))
% 3.15/3.41          | ~ (r1_tarski @ sk_A_1 @ X0))),
% 3.15/3.41      inference('demod', [status(thm)], ['113', '114', '115'])).
% 3.15/3.41  thf('117', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         (~ (v1_relat_1 @ sk_C_1)
% 3.15/3.41          | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.41          | ~ (r1_tarski @ sk_A_1 @ X0)
% 3.15/3.41          | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41             (k1_zfmisc_1 @ 
% 3.15/3.41              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ X0))))),
% 3.15/3.41      inference('sup-', [status(thm)], ['92', '116'])).
% 3.15/3.41  thf('118', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.41      inference('sup-', [status(thm)], ['2', '3'])).
% 3.15/3.41  thf('119', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('120', plain,
% 3.15/3.41      (![X0 : $i]:
% 3.15/3.41         (~ (r1_tarski @ sk_A_1 @ X0)
% 3.15/3.41          | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41             (k1_zfmisc_1 @ 
% 3.15/3.41              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ X0))))),
% 3.15/3.41      inference('demod', [status(thm)], ['117', '118', '119'])).
% 3.15/3.41  thf('121', plain,
% 3.15/3.41      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41        (k1_zfmisc_1 @ 
% 3.15/3.41         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A_1)))),
% 3.15/3.41      inference('sup-', [status(thm)], ['91', '120'])).
% 3.15/3.41  thf('122', plain,
% 3.15/3.41      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C_1) @ sk_A_1)))
% 3.15/3.41        | ~ (v1_relat_1 @ sk_C_1)
% 3.15/3.41        | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.41        | ~ (v2_funct_1 @ sk_C_1))),
% 3.15/3.41      inference('sup+', [status(thm)], ['90', '121'])).
% 3.15/3.41  thf('123', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 3.15/3.41      inference('sup+', [status(thm)], ['14', '15'])).
% 3.15/3.41  thf('124', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.41      inference('sup-', [status(thm)], ['2', '3'])).
% 3.15/3.41  thf('125', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('126', plain, ((v2_funct_1 @ sk_C_1)),
% 3.15/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.41  thf('127', plain,
% 3.15/3.41      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.15/3.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.15/3.41      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 3.15/3.41  thf('128', plain, ($false), inference('demod', [status(thm)], ['89', '127'])).
% 3.15/3.41  
% 3.15/3.41  % SZS output end Refutation
% 3.15/3.41  
% 3.27/3.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
