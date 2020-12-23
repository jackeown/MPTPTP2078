%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bqJmEcn41X

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:31 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 490 expanded)
%              Number of leaves         :   35 ( 156 expanded)
%              Depth                    :   19
%              Number of atoms          : 1345 (7323 expanded)
%              Number of equality atoms :   66 ( 304 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('21',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['34','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('67',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('68',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X27: $i] :
      ( ( v1_funct_2 @ X27 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['64','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','83','84'])).

thf('86',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','85'])).

thf('87',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('89',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('90',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('91',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['87','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('108',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('112',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','83','84'])).

thf('114',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','114','115','116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['86','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bqJmEcn41X
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.28/2.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.28/2.51  % Solved by: fo/fo7.sh
% 2.28/2.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.28/2.51  % done 2130 iterations in 2.047s
% 2.28/2.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.28/2.51  % SZS output start Refutation
% 2.28/2.51  thf(sk_A_type, type, sk_A: $i).
% 2.28/2.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.28/2.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.28/2.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.28/2.51  thf(sk_B_type, type, sk_B: $i).
% 2.28/2.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.28/2.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.28/2.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.28/2.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.28/2.51  thf(sk_C_type, type, sk_C: $i).
% 2.28/2.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.28/2.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.28/2.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.28/2.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.28/2.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.28/2.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.28/2.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.28/2.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.28/2.51  thf(t31_funct_2, conjecture,
% 2.28/2.51    (![A:$i,B:$i,C:$i]:
% 2.28/2.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.28/2.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.28/2.51       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.28/2.51         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.28/2.51           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.28/2.51           ( m1_subset_1 @
% 2.28/2.51             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.28/2.51  thf(zf_stmt_0, negated_conjecture,
% 2.28/2.51    (~( ![A:$i,B:$i,C:$i]:
% 2.28/2.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.28/2.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.28/2.51          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.28/2.51            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.28/2.51              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.28/2.51              ( m1_subset_1 @
% 2.28/2.51                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.28/2.51    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.28/2.51  thf('0', plain,
% 2.28/2.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.28/2.51        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.28/2.51        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('1', plain,
% 2.28/2.51      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.28/2.51         <= (~
% 2.28/2.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.28/2.51      inference('split', [status(esa)], ['0'])).
% 2.28/2.51  thf('2', plain,
% 2.28/2.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf(cc2_relat_1, axiom,
% 2.28/2.51    (![A:$i]:
% 2.28/2.51     ( ( v1_relat_1 @ A ) =>
% 2.28/2.51       ( ![B:$i]:
% 2.28/2.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.28/2.51  thf('3', plain,
% 2.28/2.51      (![X5 : $i, X6 : $i]:
% 2.28/2.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.28/2.51          | (v1_relat_1 @ X5)
% 2.28/2.51          | ~ (v1_relat_1 @ X6))),
% 2.28/2.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.28/2.51  thf('4', plain,
% 2.28/2.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.28/2.51      inference('sup-', [status(thm)], ['2', '3'])).
% 2.28/2.51  thf(fc6_relat_1, axiom,
% 2.28/2.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.28/2.51  thf('5', plain,
% 2.28/2.51      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.28/2.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.28/2.51  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 2.28/2.51      inference('demod', [status(thm)], ['4', '5'])).
% 2.28/2.51  thf(dt_k2_funct_1, axiom,
% 2.28/2.51    (![A:$i]:
% 2.28/2.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.28/2.51       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.28/2.51         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.28/2.51  thf('7', plain,
% 2.28/2.51      (![X11 : $i]:
% 2.28/2.51         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.28/2.51          | ~ (v1_funct_1 @ X11)
% 2.28/2.51          | ~ (v1_relat_1 @ X11))),
% 2.28/2.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.28/2.51  thf('8', plain,
% 2.28/2.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.28/2.51         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.28/2.51      inference('split', [status(esa)], ['0'])).
% 2.28/2.51  thf('9', plain,
% 2.28/2.51      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 2.28/2.51         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['7', '8'])).
% 2.28/2.51  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('11', plain,
% 2.28/2.51      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.28/2.51      inference('demod', [status(thm)], ['9', '10'])).
% 2.28/2.51  thf('12', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.28/2.51      inference('sup-', [status(thm)], ['6', '11'])).
% 2.28/2.51  thf('13', plain,
% 2.28/2.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('split', [status(esa)], ['0'])).
% 2.28/2.51  thf('14', plain,
% 2.28/2.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf(redefinition_k2_relset_1, axiom,
% 2.28/2.51    (![A:$i,B:$i,C:$i]:
% 2.28/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.28/2.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.28/2.51  thf('15', plain,
% 2.28/2.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.28/2.51         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 2.28/2.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.28/2.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.28/2.51  thf('16', plain,
% 2.28/2.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.28/2.51      inference('sup-', [status(thm)], ['14', '15'])).
% 2.28/2.51  thf('17', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('18', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.28/2.51      inference('sup+', [status(thm)], ['16', '17'])).
% 2.28/2.51  thf(d1_funct_2, axiom,
% 2.28/2.51    (![A:$i,B:$i,C:$i]:
% 2.28/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.28/2.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.28/2.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.28/2.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.28/2.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.28/2.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.28/2.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.28/2.51  thf(zf_stmt_1, axiom,
% 2.28/2.51    (![B:$i,A:$i]:
% 2.28/2.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.28/2.51       ( zip_tseitin_0 @ B @ A ) ))).
% 2.28/2.51  thf('19', plain,
% 2.28/2.51      (![X19 : $i, X20 : $i]:
% 2.28/2.51         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.28/2.51  thf('20', plain,
% 2.28/2.51      (![X11 : $i]:
% 2.28/2.51         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.28/2.51          | ~ (v1_funct_1 @ X11)
% 2.28/2.51          | ~ (v1_relat_1 @ X11))),
% 2.28/2.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.28/2.51  thf(t55_funct_1, axiom,
% 2.28/2.51    (![A:$i]:
% 2.28/2.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.28/2.51       ( ( v2_funct_1 @ A ) =>
% 2.28/2.51         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.28/2.51           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.28/2.51  thf('21', plain,
% 2.28/2.51      (![X12 : $i]:
% 2.28/2.51         (~ (v2_funct_1 @ X12)
% 2.28/2.51          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.28/2.51          | ~ (v1_funct_1 @ X12)
% 2.28/2.51          | ~ (v1_relat_1 @ X12))),
% 2.28/2.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.28/2.51  thf(t64_relat_1, axiom,
% 2.28/2.51    (![A:$i]:
% 2.28/2.51     ( ( v1_relat_1 @ A ) =>
% 2.28/2.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.28/2.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.28/2.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.28/2.51  thf('22', plain,
% 2.28/2.51      (![X9 : $i]:
% 2.28/2.51         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 2.28/2.51          | ((X9) = (k1_xboole_0))
% 2.28/2.51          | ~ (v1_relat_1 @ X9))),
% 2.28/2.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.28/2.51  thf('23', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.28/2.51          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 2.28/2.51      inference('sup-', [status(thm)], ['21', '22'])).
% 2.28/2.51  thf('24', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 2.28/2.51      inference('sup-', [status(thm)], ['20', '23'])).
% 2.28/2.51  thf('25', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0))),
% 2.28/2.51      inference('simplify', [status(thm)], ['24'])).
% 2.28/2.51  thf('26', plain,
% 2.28/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.51         (((k2_relat_1 @ X1) != (X0))
% 2.28/2.51          | (zip_tseitin_0 @ X0 @ X2)
% 2.28/2.51          | ~ (v1_relat_1 @ X1)
% 2.28/2.51          | ~ (v1_funct_1 @ X1)
% 2.28/2.51          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 2.28/2.51          | ~ (v2_funct_1 @ X1))),
% 2.28/2.51      inference('sup-', [status(thm)], ['19', '25'])).
% 2.28/2.51  thf('27', plain,
% 2.28/2.51      (![X1 : $i, X2 : $i]:
% 2.28/2.51         (~ (v2_funct_1 @ X1)
% 2.28/2.51          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 2.28/2.51          | ~ (v1_funct_1 @ X1)
% 2.28/2.51          | ~ (v1_relat_1 @ X1)
% 2.28/2.51          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 2.28/2.51      inference('simplify', [status(thm)], ['26'])).
% 2.28/2.51  thf('28', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((zip_tseitin_0 @ sk_B @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ sk_C)
% 2.28/2.51          | ~ (v1_funct_1 @ sk_C)
% 2.28/2.51          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 2.28/2.51          | ~ (v2_funct_1 @ sk_C))),
% 2.28/2.51      inference('sup+', [status(thm)], ['18', '27'])).
% 2.28/2.51  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 2.28/2.51      inference('demod', [status(thm)], ['4', '5'])).
% 2.28/2.51  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('31', plain, ((v2_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('32', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 2.28/2.51      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 2.28/2.51  thf('33', plain,
% 2.28/2.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('split', [status(esa)], ['0'])).
% 2.28/2.51  thf('34', plain,
% 2.28/2.51      ((![X0 : $i]:
% 2.28/2.51          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 2.28/2.51           | (zip_tseitin_0 @ sk_B @ X0)))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('sup-', [status(thm)], ['32', '33'])).
% 2.28/2.51  thf('35', plain,
% 2.28/2.51      (![X19 : $i, X20 : $i]:
% 2.28/2.51         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.28/2.51  thf(t4_subset_1, axiom,
% 2.28/2.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.28/2.51  thf('36', plain,
% 2.28/2.51      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 2.28/2.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.28/2.51  thf(redefinition_k1_relset_1, axiom,
% 2.28/2.51    (![A:$i,B:$i,C:$i]:
% 2.28/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.28/2.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.28/2.51  thf('37', plain,
% 2.28/2.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.28/2.51         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 2.28/2.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.28/2.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.28/2.51  thf('38', plain,
% 2.28/2.51      (![X0 : $i, X1 : $i]:
% 2.28/2.51         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.28/2.51      inference('sup-', [status(thm)], ['36', '37'])).
% 2.28/2.51  thf(t60_relat_1, axiom,
% 2.28/2.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.28/2.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.28/2.51  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.28/2.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.28/2.51  thf('40', plain,
% 2.28/2.51      (![X0 : $i, X1 : $i]:
% 2.28/2.51         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.28/2.51      inference('demod', [status(thm)], ['38', '39'])).
% 2.28/2.51  thf(zf_stmt_2, axiom,
% 2.28/2.51    (![C:$i,B:$i,A:$i]:
% 2.28/2.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.28/2.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.28/2.51  thf('41', plain,
% 2.28/2.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.28/2.51         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 2.28/2.51          | (v1_funct_2 @ X23 @ X21 @ X22)
% 2.28/2.51          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.28/2.51  thf('42', plain,
% 2.28/2.51      (![X0 : $i, X1 : $i]:
% 2.28/2.51         (((X1) != (k1_xboole_0))
% 2.28/2.51          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 2.28/2.51          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 2.28/2.51      inference('sup-', [status(thm)], ['40', '41'])).
% 2.28/2.51  thf('43', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.28/2.51          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.28/2.51      inference('simplify', [status(thm)], ['42'])).
% 2.28/2.51  thf('44', plain,
% 2.28/2.51      (![X19 : $i, X20 : $i]:
% 2.28/2.51         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.28/2.51  thf('45', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 2.28/2.51      inference('simplify', [status(thm)], ['44'])).
% 2.28/2.51  thf('46', plain,
% 2.28/2.51      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 2.28/2.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.28/2.51  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.28/2.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.28/2.51  thf(zf_stmt_5, axiom,
% 2.28/2.51    (![A:$i,B:$i,C:$i]:
% 2.28/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.28/2.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.28/2.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.28/2.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.28/2.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.28/2.51  thf('47', plain,
% 2.28/2.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.28/2.51         (~ (zip_tseitin_0 @ X24 @ X25)
% 2.28/2.51          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 2.28/2.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.28/2.51  thf('48', plain,
% 2.28/2.51      (![X0 : $i, X1 : $i]:
% 2.28/2.51         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.28/2.51      inference('sup-', [status(thm)], ['46', '47'])).
% 2.28/2.51  thf('49', plain,
% 2.28/2.51      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.28/2.51      inference('sup-', [status(thm)], ['45', '48'])).
% 2.28/2.51  thf('50', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.28/2.51      inference('demod', [status(thm)], ['43', '49'])).
% 2.28/2.51  thf('51', plain,
% 2.28/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.51         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 2.28/2.51      inference('sup+', [status(thm)], ['35', '50'])).
% 2.28/2.51  thf('52', plain,
% 2.28/2.51      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('clc', [status(thm)], ['34', '51'])).
% 2.28/2.51  thf('53', plain,
% 2.28/2.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('54', plain,
% 2.28/2.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.28/2.51         (~ (zip_tseitin_0 @ X24 @ X25)
% 2.28/2.51          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 2.28/2.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.28/2.51  thf('55', plain,
% 2.28/2.51      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.28/2.51      inference('sup-', [status(thm)], ['53', '54'])).
% 2.28/2.51  thf('56', plain,
% 2.28/2.51      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('sup-', [status(thm)], ['52', '55'])).
% 2.28/2.51  thf('57', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('58', plain,
% 2.28/2.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.28/2.51         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 2.28/2.51          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 2.28/2.51          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.28/2.51  thf('59', plain,
% 2.28/2.51      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.28/2.51        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.51      inference('sup-', [status(thm)], ['57', '58'])).
% 2.28/2.51  thf('60', plain,
% 2.28/2.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('61', plain,
% 2.28/2.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.28/2.51         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 2.28/2.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.28/2.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.28/2.51  thf('62', plain,
% 2.28/2.51      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.28/2.51      inference('sup-', [status(thm)], ['60', '61'])).
% 2.28/2.51  thf('63', plain,
% 2.28/2.51      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.28/2.51      inference('demod', [status(thm)], ['59', '62'])).
% 2.28/2.51  thf('64', plain,
% 2.28/2.51      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('sup-', [status(thm)], ['56', '63'])).
% 2.28/2.51  thf('65', plain,
% 2.28/2.51      (![X12 : $i]:
% 2.28/2.51         (~ (v2_funct_1 @ X12)
% 2.28/2.51          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.28/2.51          | ~ (v1_funct_1 @ X12)
% 2.28/2.51          | ~ (v1_relat_1 @ X12))),
% 2.28/2.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.28/2.51  thf('66', plain,
% 2.28/2.51      (![X11 : $i]:
% 2.28/2.51         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.28/2.51          | ~ (v1_funct_1 @ X11)
% 2.28/2.51          | ~ (v1_relat_1 @ X11))),
% 2.28/2.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.28/2.51  thf('67', plain,
% 2.28/2.51      (![X11 : $i]:
% 2.28/2.51         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.28/2.51          | ~ (v1_funct_1 @ X11)
% 2.28/2.51          | ~ (v1_relat_1 @ X11))),
% 2.28/2.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.28/2.51  thf('68', plain,
% 2.28/2.51      (![X12 : $i]:
% 2.28/2.51         (~ (v2_funct_1 @ X12)
% 2.28/2.51          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.28/2.51          | ~ (v1_funct_1 @ X12)
% 2.28/2.51          | ~ (v1_relat_1 @ X12))),
% 2.28/2.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.28/2.51  thf(t3_funct_2, axiom,
% 2.28/2.51    (![A:$i]:
% 2.28/2.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.28/2.51       ( ( v1_funct_1 @ A ) & 
% 2.28/2.51         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.28/2.51         ( m1_subset_1 @
% 2.28/2.51           A @ 
% 2.28/2.51           ( k1_zfmisc_1 @
% 2.28/2.51             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.28/2.51  thf('69', plain,
% 2.28/2.51      (![X27 : $i]:
% 2.28/2.51         ((v1_funct_2 @ X27 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27))
% 2.28/2.51          | ~ (v1_funct_1 @ X27)
% 2.28/2.51          | ~ (v1_relat_1 @ X27))),
% 2.28/2.51      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.28/2.51  thf('70', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.28/2.51           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.28/2.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.28/2.51      inference('sup+', [status(thm)], ['68', '69'])).
% 2.28/2.51  thf('71', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.28/2.51             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['67', '70'])).
% 2.28/2.51  thf('72', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.28/2.51           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0))),
% 2.28/2.51      inference('simplify', [status(thm)], ['71'])).
% 2.28/2.51  thf('73', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.28/2.51             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['66', '72'])).
% 2.28/2.51  thf('74', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.28/2.51           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0))),
% 2.28/2.51      inference('simplify', [status(thm)], ['73'])).
% 2.28/2.51  thf('75', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.28/2.51           (k1_relat_1 @ X0))
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v2_funct_1 @ X0))),
% 2.28/2.51      inference('sup+', [status(thm)], ['65', '74'])).
% 2.28/2.51  thf('76', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.28/2.51             (k1_relat_1 @ X0)))),
% 2.28/2.51      inference('simplify', [status(thm)], ['75'])).
% 2.28/2.51  thf('77', plain,
% 2.28/2.51      ((((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 2.28/2.51         | ~ (v1_relat_1 @ sk_C)
% 2.28/2.51         | ~ (v1_funct_1 @ sk_C)
% 2.28/2.51         | ~ (v2_funct_1 @ sk_C)))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('sup+', [status(thm)], ['64', '76'])).
% 2.28/2.51  thf('78', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.28/2.51      inference('sup+', [status(thm)], ['16', '17'])).
% 2.28/2.51  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 2.28/2.51      inference('demod', [status(thm)], ['4', '5'])).
% 2.28/2.51  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('82', plain,
% 2.28/2.51      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.28/2.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.28/2.51      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 2.28/2.51  thf('83', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.28/2.51      inference('demod', [status(thm)], ['13', '82'])).
% 2.28/2.51  thf('84', plain,
% 2.28/2.51      (~
% 2.28/2.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 2.28/2.51       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 2.28/2.51       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.28/2.51      inference('split', [status(esa)], ['0'])).
% 2.28/2.51  thf('85', plain,
% 2.28/2.51      (~
% 2.28/2.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.28/2.51      inference('sat_resolution*', [status(thm)], ['12', '83', '84'])).
% 2.28/2.51  thf('86', plain,
% 2.28/2.51      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.28/2.51      inference('simpl_trail', [status(thm)], ['1', '85'])).
% 2.28/2.51  thf('87', plain,
% 2.28/2.51      (![X12 : $i]:
% 2.28/2.51         (~ (v2_funct_1 @ X12)
% 2.28/2.51          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 2.28/2.51          | ~ (v1_funct_1 @ X12)
% 2.28/2.51          | ~ (v1_relat_1 @ X12))),
% 2.28/2.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.28/2.51  thf('88', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.28/2.51      inference('sup+', [status(thm)], ['16', '17'])).
% 2.28/2.51  thf('89', plain,
% 2.28/2.51      (![X11 : $i]:
% 2.28/2.51         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 2.28/2.51          | ~ (v1_funct_1 @ X11)
% 2.28/2.51          | ~ (v1_relat_1 @ X11))),
% 2.28/2.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.28/2.51  thf('90', plain,
% 2.28/2.51      (![X11 : $i]:
% 2.28/2.51         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 2.28/2.51          | ~ (v1_funct_1 @ X11)
% 2.28/2.51          | ~ (v1_relat_1 @ X11))),
% 2.28/2.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.28/2.51  thf('91', plain,
% 2.28/2.51      (![X12 : $i]:
% 2.28/2.51         (~ (v2_funct_1 @ X12)
% 2.28/2.51          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.28/2.51          | ~ (v1_funct_1 @ X12)
% 2.28/2.51          | ~ (v1_relat_1 @ X12))),
% 2.28/2.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.28/2.51  thf('92', plain,
% 2.28/2.51      (![X27 : $i]:
% 2.28/2.51         ((m1_subset_1 @ X27 @ 
% 2.28/2.51           (k1_zfmisc_1 @ 
% 2.28/2.51            (k2_zfmisc_1 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27))))
% 2.28/2.51          | ~ (v1_funct_1 @ X27)
% 2.28/2.51          | ~ (v1_relat_1 @ X27))),
% 2.28/2.51      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.28/2.51  thf('93', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.28/2.51           (k1_zfmisc_1 @ 
% 2.28/2.51            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.28/2.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.28/2.51      inference('sup+', [status(thm)], ['91', '92'])).
% 2.28/2.51  thf('94', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.28/2.51             (k1_zfmisc_1 @ 
% 2.28/2.51              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.28/2.51               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['90', '93'])).
% 2.28/2.51  thf('95', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.28/2.51           (k1_zfmisc_1 @ 
% 2.28/2.51            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0))),
% 2.28/2.51      inference('simplify', [status(thm)], ['94'])).
% 2.28/2.51  thf('96', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         (~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.28/2.51             (k1_zfmisc_1 @ 
% 2.28/2.51              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.28/2.51               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['89', '95'])).
% 2.28/2.51  thf('97', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.28/2.51           (k1_zfmisc_1 @ 
% 2.28/2.51            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.28/2.51          | ~ (v2_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_funct_1 @ X0)
% 2.28/2.51          | ~ (v1_relat_1 @ X0))),
% 2.28/2.51      inference('simplify', [status(thm)], ['96'])).
% 2.28/2.51  thf('98', plain,
% 2.28/2.51      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51         (k1_zfmisc_1 @ 
% 2.28/2.51          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.28/2.51        | ~ (v1_relat_1 @ sk_C)
% 2.28/2.51        | ~ (v1_funct_1 @ sk_C)
% 2.28/2.51        | ~ (v2_funct_1 @ sk_C))),
% 2.28/2.51      inference('sup+', [status(thm)], ['88', '97'])).
% 2.28/2.51  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 2.28/2.51      inference('demod', [status(thm)], ['4', '5'])).
% 2.28/2.51  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('102', plain,
% 2.28/2.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51        (k1_zfmisc_1 @ 
% 2.28/2.51         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.28/2.51      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 2.28/2.51  thf('103', plain,
% 2.28/2.51      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 2.28/2.51        | ~ (v1_relat_1 @ sk_C)
% 2.28/2.51        | ~ (v1_funct_1 @ sk_C)
% 2.28/2.51        | ~ (v2_funct_1 @ sk_C))),
% 2.28/2.51      inference('sup+', [status(thm)], ['87', '102'])).
% 2.28/2.51  thf('104', plain,
% 2.28/2.51      (![X0 : $i]:
% 2.28/2.51         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 2.28/2.51      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 2.28/2.51  thf('105', plain,
% 2.28/2.51      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.28/2.51         <= (~
% 2.28/2.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.28/2.51      inference('split', [status(esa)], ['0'])).
% 2.28/2.51  thf('106', plain,
% 2.28/2.51      ((![X0 : $i]:
% 2.28/2.51          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 2.28/2.51              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.28/2.51           | (zip_tseitin_0 @ sk_B @ X0)))
% 2.28/2.51         <= (~
% 2.28/2.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['104', '105'])).
% 2.28/2.51  thf('107', plain,
% 2.28/2.51      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 2.28/2.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.28/2.51  thf('108', plain,
% 2.28/2.51      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 2.28/2.51         <= (~
% 2.28/2.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.28/2.51      inference('demod', [status(thm)], ['106', '107'])).
% 2.28/2.51  thf('109', plain,
% 2.28/2.51      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.28/2.51      inference('sup-', [status(thm)], ['53', '54'])).
% 2.28/2.51  thf('110', plain,
% 2.28/2.51      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 2.28/2.51         <= (~
% 2.28/2.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['108', '109'])).
% 2.28/2.51  thf('111', plain,
% 2.28/2.51      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.28/2.51      inference('demod', [status(thm)], ['59', '62'])).
% 2.28/2.51  thf('112', plain,
% 2.28/2.51      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.28/2.51         <= (~
% 2.28/2.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.28/2.51      inference('sup-', [status(thm)], ['110', '111'])).
% 2.28/2.51  thf('113', plain,
% 2.28/2.51      (~
% 2.28/2.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.28/2.51      inference('sat_resolution*', [status(thm)], ['12', '83', '84'])).
% 2.28/2.51  thf('114', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.28/2.51      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 2.28/2.51  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 2.28/2.51      inference('demod', [status(thm)], ['4', '5'])).
% 2.28/2.51  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 2.28/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.51  thf('118', plain,
% 2.28/2.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.28/2.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.28/2.51      inference('demod', [status(thm)], ['103', '114', '115', '116', '117'])).
% 2.28/2.51  thf('119', plain, ($false), inference('demod', [status(thm)], ['86', '118'])).
% 2.28/2.51  
% 2.28/2.51  % SZS output end Refutation
% 2.28/2.51  
% 2.28/2.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
