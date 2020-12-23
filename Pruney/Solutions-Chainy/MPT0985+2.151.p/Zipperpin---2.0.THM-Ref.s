%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s3lst2OtEx

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:48 EST 2020

% Result     : Theorem 3.11s
% Output     : Refutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 527 expanded)
%              Number of leaves         :   37 ( 168 expanded)
%              Depth                    :   25
%              Number of atoms          : 1434 (7814 expanded)
%              Number of equality atoms :   67 ( 317 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
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
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A_1 )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(clc,[status(thm)],['34','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( sk_A_1
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('66',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('67',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('68',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
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
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

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
    inference('sup-',[status(thm)],['66','75'])).

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
    inference('sup+',[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference('sup+',[status(thm)],['64','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['13','85'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','86','87'])).

thf('89',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','88'])).

thf('90',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('92',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('100',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('102',plain,
    ( ( sk_A_1
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ X32 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A_1 @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A_1 @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','86','87'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ sk_A_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['91','120'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['90','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['89','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s3lst2OtEx
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.11/3.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.11/3.35  % Solved by: fo/fo7.sh
% 3.11/3.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.11/3.35  % done 3253 iterations in 2.892s
% 3.11/3.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.11/3.35  % SZS output start Refutation
% 3.11/3.35  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.11/3.35  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.11/3.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.11/3.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.11/3.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.11/3.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.11/3.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.11/3.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.11/3.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.11/3.35  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.11/3.35  thf(sk_A_1_type, type, sk_A_1: $i).
% 3.11/3.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.11/3.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.11/3.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.11/3.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.11/3.35  thf(sk_B_type, type, sk_B: $i).
% 3.11/3.35  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.11/3.35  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.11/3.35  thf(sk_C_type, type, sk_C: $i).
% 3.11/3.35  thf(t31_funct_2, conjecture,
% 3.11/3.35    (![A:$i,B:$i,C:$i]:
% 3.11/3.35     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.11/3.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.11/3.35       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.11/3.35         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.11/3.35           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.11/3.35           ( m1_subset_1 @
% 3.11/3.35             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.11/3.35  thf(zf_stmt_0, negated_conjecture,
% 3.11/3.35    (~( ![A:$i,B:$i,C:$i]:
% 3.11/3.35        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.11/3.35            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.11/3.35          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.11/3.35            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.11/3.35              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.11/3.35              ( m1_subset_1 @
% 3.11/3.35                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 3.11/3.35    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 3.11/3.35  thf('0', plain,
% 3.11/3.35      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.11/3.35        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)
% 3.11/3.35        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('1', plain,
% 3.11/3.35      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('split', [status(esa)], ['0'])).
% 3.11/3.35  thf('2', plain,
% 3.11/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf(cc2_relat_1, axiom,
% 3.11/3.35    (![A:$i]:
% 3.11/3.35     ( ( v1_relat_1 @ A ) =>
% 3.11/3.35       ( ![B:$i]:
% 3.11/3.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.11/3.35  thf('3', plain,
% 3.11/3.35      (![X8 : $i, X9 : $i]:
% 3.11/3.35         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 3.11/3.35          | (v1_relat_1 @ X8)
% 3.11/3.35          | ~ (v1_relat_1 @ X9))),
% 3.11/3.35      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.11/3.35  thf('4', plain,
% 3.11/3.35      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.11/3.35      inference('sup-', [status(thm)], ['2', '3'])).
% 3.11/3.35  thf(fc6_relat_1, axiom,
% 3.11/3.35    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.11/3.35  thf('5', plain,
% 3.11/3.35      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 3.11/3.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.11/3.35  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 3.11/3.35      inference('demod', [status(thm)], ['4', '5'])).
% 3.11/3.35  thf(dt_k2_funct_1, axiom,
% 3.11/3.35    (![A:$i]:
% 3.11/3.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.11/3.35       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.11/3.35         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.11/3.35  thf('7', plain,
% 3.11/3.35      (![X15 : $i]:
% 3.11/3.35         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 3.11/3.35          | ~ (v1_funct_1 @ X15)
% 3.11/3.35          | ~ (v1_relat_1 @ X15))),
% 3.11/3.35      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.11/3.35  thf('8', plain,
% 3.11/3.35      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.11/3.35         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.11/3.35      inference('split', [status(esa)], ['0'])).
% 3.11/3.35  thf('9', plain,
% 3.11/3.35      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 3.11/3.35         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['7', '8'])).
% 3.11/3.35  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('11', plain,
% 3.11/3.35      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.11/3.35      inference('demod', [status(thm)], ['9', '10'])).
% 3.11/3.35  thf('12', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['6', '11'])).
% 3.11/3.35  thf('13', plain,
% 3.11/3.35      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('split', [status(esa)], ['0'])).
% 3.11/3.35  thf('14', plain,
% 3.11/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf(redefinition_k2_relset_1, axiom,
% 3.11/3.35    (![A:$i,B:$i,C:$i]:
% 3.11/3.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.11/3.35       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.11/3.35  thf('15', plain,
% 3.11/3.35      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.11/3.35         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 3.11/3.35          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.11/3.35      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.11/3.35  thf('16', plain,
% 3.11/3.35      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.11/3.35      inference('sup-', [status(thm)], ['14', '15'])).
% 3.11/3.35  thf('17', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('18', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.11/3.35      inference('sup+', [status(thm)], ['16', '17'])).
% 3.11/3.35  thf(d1_funct_2, axiom,
% 3.11/3.35    (![A:$i,B:$i,C:$i]:
% 3.11/3.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.11/3.35       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.11/3.35           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.11/3.35             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.11/3.35         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.11/3.35           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.11/3.35             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.11/3.35  thf(zf_stmt_1, axiom,
% 3.11/3.35    (![B:$i,A:$i]:
% 3.11/3.35     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.11/3.35       ( zip_tseitin_0 @ B @ A ) ))).
% 3.11/3.35  thf('19', plain,
% 3.11/3.35      (![X23 : $i, X24 : $i]:
% 3.11/3.35         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.11/3.35  thf('20', plain,
% 3.11/3.35      (![X15 : $i]:
% 3.11/3.35         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 3.11/3.35          | ~ (v1_funct_1 @ X15)
% 3.11/3.35          | ~ (v1_relat_1 @ X15))),
% 3.11/3.35      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.11/3.35  thf(t55_funct_1, axiom,
% 3.11/3.35    (![A:$i]:
% 3.11/3.35     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.11/3.35       ( ( v2_funct_1 @ A ) =>
% 3.11/3.35         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.11/3.35           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.11/3.35  thf('21', plain,
% 3.11/3.35      (![X16 : $i]:
% 3.11/3.35         (~ (v2_funct_1 @ X16)
% 3.11/3.35          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 3.11/3.35          | ~ (v1_funct_1 @ X16)
% 3.11/3.35          | ~ (v1_relat_1 @ X16))),
% 3.11/3.35      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.11/3.35  thf(t64_relat_1, axiom,
% 3.11/3.35    (![A:$i]:
% 3.11/3.35     ( ( v1_relat_1 @ A ) =>
% 3.11/3.35       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 3.11/3.35           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.11/3.35         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.11/3.35  thf('22', plain,
% 3.11/3.35      (![X12 : $i]:
% 3.11/3.35         (((k1_relat_1 @ X12) != (k1_xboole_0))
% 3.11/3.35          | ((X12) = (k1_xboole_0))
% 3.11/3.35          | ~ (v1_relat_1 @ X12))),
% 3.11/3.35      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.11/3.35  thf('23', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.11/3.35          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['21', '22'])).
% 3.11/3.35  thf('24', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['20', '23'])).
% 3.11/3.35  thf('25', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0))),
% 3.11/3.35      inference('simplify', [status(thm)], ['24'])).
% 3.11/3.35  thf('26', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.11/3.35         (((k2_relat_1 @ X1) != (X0))
% 3.11/3.35          | (zip_tseitin_0 @ X0 @ X2)
% 3.11/3.35          | ~ (v1_relat_1 @ X1)
% 3.11/3.35          | ~ (v1_funct_1 @ X1)
% 3.11/3.35          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.11/3.35          | ~ (v2_funct_1 @ X1))),
% 3.11/3.35      inference('sup-', [status(thm)], ['19', '25'])).
% 3.11/3.35  thf('27', plain,
% 3.11/3.35      (![X1 : $i, X2 : $i]:
% 3.11/3.35         (~ (v2_funct_1 @ X1)
% 3.11/3.35          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.11/3.35          | ~ (v1_funct_1 @ X1)
% 3.11/3.35          | ~ (v1_relat_1 @ X1)
% 3.11/3.35          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 3.11/3.35      inference('simplify', [status(thm)], ['26'])).
% 3.11/3.35  thf('28', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((zip_tseitin_0 @ sk_B @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ sk_C)
% 3.11/3.35          | ~ (v1_funct_1 @ sk_C)
% 3.11/3.35          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 3.11/3.35          | ~ (v2_funct_1 @ sk_C))),
% 3.11/3.35      inference('sup+', [status(thm)], ['18', '27'])).
% 3.11/3.35  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 3.11/3.35      inference('demod', [status(thm)], ['4', '5'])).
% 3.11/3.35  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('31', plain, ((v2_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('32', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 3.11/3.35      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 3.11/3.35  thf('33', plain,
% 3.11/3.35      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('split', [status(esa)], ['0'])).
% 3.11/3.35  thf('34', plain,
% 3.11/3.35      ((![X0 : $i]:
% 3.11/3.35          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A_1)
% 3.11/3.35           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['32', '33'])).
% 3.11/3.35  thf('35', plain,
% 3.11/3.35      (![X23 : $i, X24 : $i]:
% 3.11/3.35         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.11/3.35  thf(t4_subset_1, axiom,
% 3.11/3.35    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.11/3.35  thf('36', plain,
% 3.11/3.35      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.11/3.35      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.11/3.35  thf(redefinition_k1_relset_1, axiom,
% 3.11/3.35    (![A:$i,B:$i,C:$i]:
% 3.11/3.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.11/3.35       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.11/3.35  thf('37', plain,
% 3.11/3.35      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.11/3.35         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 3.11/3.35          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.11/3.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.11/3.35  thf('38', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i]:
% 3.11/3.35         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.11/3.35      inference('sup-', [status(thm)], ['36', '37'])).
% 3.11/3.35  thf(t60_relat_1, axiom,
% 3.11/3.35    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.11/3.35     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.11/3.35  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.11/3.35      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.11/3.35  thf('40', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i]:
% 3.11/3.35         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.11/3.35      inference('demod', [status(thm)], ['38', '39'])).
% 3.11/3.35  thf(zf_stmt_2, axiom,
% 3.11/3.35    (![C:$i,B:$i,A:$i]:
% 3.11/3.35     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.11/3.35       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.11/3.35  thf('41', plain,
% 3.11/3.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.11/3.35         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 3.11/3.35          | (v1_funct_2 @ X27 @ X25 @ X26)
% 3.11/3.35          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.11/3.35  thf('42', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i]:
% 3.11/3.35         (((X1) != (k1_xboole_0))
% 3.11/3.35          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.11/3.35          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.11/3.35      inference('sup-', [status(thm)], ['40', '41'])).
% 3.11/3.35  thf('43', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.11/3.35          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.11/3.35      inference('simplify', [status(thm)], ['42'])).
% 3.11/3.35  thf('44', plain,
% 3.11/3.35      (![X23 : $i, X24 : $i]:
% 3.11/3.35         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.11/3.35  thf('45', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 3.11/3.35      inference('simplify', [status(thm)], ['44'])).
% 3.11/3.35  thf('46', plain,
% 3.11/3.35      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.11/3.35      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.11/3.35  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.11/3.35  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.11/3.35  thf(zf_stmt_5, axiom,
% 3.11/3.35    (![A:$i,B:$i,C:$i]:
% 3.11/3.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.11/3.35       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.11/3.35         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.11/3.35           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.11/3.35             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.11/3.35  thf('47', plain,
% 3.11/3.35      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.11/3.35         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.11/3.35          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.11/3.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.11/3.35  thf('48', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i]:
% 3.11/3.35         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.11/3.35      inference('sup-', [status(thm)], ['46', '47'])).
% 3.11/3.35  thf('49', plain,
% 3.11/3.35      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.11/3.35      inference('sup-', [status(thm)], ['45', '48'])).
% 3.11/3.35  thf('50', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.11/3.35      inference('demod', [status(thm)], ['43', '49'])).
% 3.11/3.35  thf('51', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.11/3.35         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.11/3.35      inference('sup+', [status(thm)], ['35', '50'])).
% 3.11/3.35  thf('52', plain,
% 3.11/3.35      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('clc', [status(thm)], ['34', '51'])).
% 3.11/3.35  thf('53', plain,
% 3.11/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('54', plain,
% 3.11/3.35      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.11/3.35         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.11/3.35          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.11/3.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.11/3.35  thf('55', plain,
% 3.11/3.35      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 3.11/3.35        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 3.11/3.35      inference('sup-', [status(thm)], ['53', '54'])).
% 3.11/3.35  thf('56', plain,
% 3.11/3.35      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['52', '55'])).
% 3.11/3.35  thf('57', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('58', plain,
% 3.11/3.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.11/3.35         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 3.11/3.35          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 3.11/3.35          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.11/3.35  thf('59', plain,
% 3.11/3.35      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 3.11/3.35        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['57', '58'])).
% 3.11/3.35  thf('60', plain,
% 3.11/3.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('61', plain,
% 3.11/3.35      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.11/3.35         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 3.11/3.35          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.11/3.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.11/3.35  thf('62', plain,
% 3.11/3.35      (((k1_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 3.11/3.35      inference('sup-', [status(thm)], ['60', '61'])).
% 3.11/3.35  thf('63', plain,
% 3.11/3.35      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 3.11/3.35        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 3.11/3.35      inference('demod', [status(thm)], ['59', '62'])).
% 3.11/3.35  thf('64', plain,
% 3.11/3.35      ((((sk_A_1) = (k1_relat_1 @ sk_C)))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['56', '63'])).
% 3.11/3.35  thf('65', plain,
% 3.11/3.35      (![X16 : $i]:
% 3.11/3.35         (~ (v2_funct_1 @ X16)
% 3.11/3.35          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 3.11/3.35          | ~ (v1_funct_1 @ X16)
% 3.11/3.35          | ~ (v1_relat_1 @ X16))),
% 3.11/3.35      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.11/3.35  thf('66', plain,
% 3.11/3.35      (![X15 : $i]:
% 3.11/3.35         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 3.11/3.35          | ~ (v1_funct_1 @ X15)
% 3.11/3.35          | ~ (v1_relat_1 @ X15))),
% 3.11/3.35      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.11/3.35  thf('67', plain,
% 3.11/3.35      (![X15 : $i]:
% 3.11/3.35         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 3.11/3.35          | ~ (v1_funct_1 @ X15)
% 3.11/3.35          | ~ (v1_relat_1 @ X15))),
% 3.11/3.35      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.11/3.35  thf('68', plain,
% 3.11/3.35      (![X16 : $i]:
% 3.11/3.35         (~ (v2_funct_1 @ X16)
% 3.11/3.35          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 3.11/3.35          | ~ (v1_funct_1 @ X16)
% 3.11/3.35          | ~ (v1_relat_1 @ X16))),
% 3.11/3.35      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.11/3.35  thf(d10_xboole_0, axiom,
% 3.11/3.35    (![A:$i,B:$i]:
% 3.11/3.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.11/3.35  thf('69', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.11/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.11/3.35  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.11/3.35      inference('simplify', [status(thm)], ['69'])).
% 3.11/3.35  thf(t4_funct_2, axiom,
% 3.11/3.35    (![A:$i,B:$i]:
% 3.11/3.35     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.11/3.35       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.11/3.35         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.11/3.35           ( m1_subset_1 @
% 3.11/3.35             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.11/3.35  thf('71', plain,
% 3.11/3.35      (![X31 : $i, X32 : $i]:
% 3.11/3.35         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 3.11/3.35          | (v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ X32)
% 3.11/3.35          | ~ (v1_funct_1 @ X31)
% 3.11/3.35          | ~ (v1_relat_1 @ X31))),
% 3.11/3.35      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.11/3.35  thf('72', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['70', '71'])).
% 3.11/3.35  thf('73', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.11/3.35           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.11/3.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.11/3.35      inference('sup+', [status(thm)], ['68', '72'])).
% 3.11/3.35  thf('74', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.11/3.35             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['67', '73'])).
% 3.11/3.35  thf('75', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.11/3.35           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0))),
% 3.11/3.35      inference('simplify', [status(thm)], ['74'])).
% 3.11/3.35  thf('76', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.11/3.35             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['66', '75'])).
% 3.11/3.35  thf('77', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.11/3.35           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0))),
% 3.11/3.35      inference('simplify', [status(thm)], ['76'])).
% 3.11/3.35  thf('78', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.11/3.35           (k1_relat_1 @ X0))
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v2_funct_1 @ X0))),
% 3.11/3.35      inference('sup+', [status(thm)], ['65', '77'])).
% 3.11/3.35  thf('79', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.11/3.35             (k1_relat_1 @ X0)))),
% 3.11/3.35      inference('simplify', [status(thm)], ['78'])).
% 3.11/3.35  thf('80', plain,
% 3.11/3.35      ((((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A_1)
% 3.11/3.35         | ~ (v1_relat_1 @ sk_C)
% 3.11/3.35         | ~ (v1_funct_1 @ sk_C)
% 3.11/3.35         | ~ (v2_funct_1 @ sk_C)))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('sup+', [status(thm)], ['64', '79'])).
% 3.11/3.35  thf('81', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.11/3.35      inference('sup+', [status(thm)], ['16', '17'])).
% 3.11/3.35  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 3.11/3.35      inference('demod', [status(thm)], ['4', '5'])).
% 3.11/3.35  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('85', plain,
% 3.11/3.35      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1))
% 3.11/3.35         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 3.11/3.35  thf('86', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1))),
% 3.11/3.35      inference('demod', [status(thm)], ['13', '85'])).
% 3.11/3.35  thf('87', plain,
% 3.11/3.35      (~
% 3.11/3.35       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))) | 
% 3.11/3.35       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A_1)) | 
% 3.11/3.35       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.11/3.35      inference('split', [status(esa)], ['0'])).
% 3.11/3.35  thf('88', plain,
% 3.11/3.35      (~
% 3.11/3.35       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 3.11/3.35      inference('sat_resolution*', [status(thm)], ['12', '86', '87'])).
% 3.11/3.35  thf('89', plain,
% 3.11/3.35      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('simpl_trail', [status(thm)], ['1', '88'])).
% 3.11/3.35  thf('90', plain,
% 3.11/3.35      (![X16 : $i]:
% 3.11/3.35         (~ (v2_funct_1 @ X16)
% 3.11/3.35          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 3.11/3.35          | ~ (v1_funct_1 @ X16)
% 3.11/3.35          | ~ (v1_relat_1 @ X16))),
% 3.11/3.35      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.11/3.35  thf('91', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.11/3.35      inference('simplify', [status(thm)], ['69'])).
% 3.11/3.35  thf('92', plain,
% 3.11/3.35      (![X15 : $i]:
% 3.11/3.35         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 3.11/3.35          | ~ (v1_funct_1 @ X15)
% 3.11/3.35          | ~ (v1_relat_1 @ X15))),
% 3.11/3.35      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.11/3.35  thf('93', plain,
% 3.11/3.35      (![X15 : $i]:
% 3.11/3.35         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 3.11/3.35          | ~ (v1_funct_1 @ X15)
% 3.11/3.35          | ~ (v1_relat_1 @ X15))),
% 3.11/3.35      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.11/3.35  thf('94', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 3.11/3.35      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 3.11/3.35  thf('95', plain,
% 3.11/3.35      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('split', [status(esa)], ['0'])).
% 3.11/3.35  thf('96', plain,
% 3.11/3.35      ((![X0 : $i]:
% 3.11/3.35          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.11/3.35              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 3.11/3.35           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['94', '95'])).
% 3.11/3.35  thf('97', plain,
% 3.11/3.35      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 3.11/3.35      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.11/3.35  thf('98', plain,
% 3.11/3.35      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('demod', [status(thm)], ['96', '97'])).
% 3.11/3.35  thf('99', plain,
% 3.11/3.35      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 3.11/3.35        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 3.11/3.35      inference('sup-', [status(thm)], ['53', '54'])).
% 3.11/3.35  thf('100', plain,
% 3.11/3.35      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['98', '99'])).
% 3.11/3.35  thf('101', plain,
% 3.11/3.35      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 3.11/3.35        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 3.11/3.35      inference('demod', [status(thm)], ['59', '62'])).
% 3.11/3.35  thf('102', plain,
% 3.11/3.35      ((((sk_A_1) = (k1_relat_1 @ sk_C)))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['100', '101'])).
% 3.11/3.35  thf('103', plain,
% 3.11/3.35      (![X16 : $i]:
% 3.11/3.35         (~ (v2_funct_1 @ X16)
% 3.11/3.35          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 3.11/3.35          | ~ (v1_funct_1 @ X16)
% 3.11/3.35          | ~ (v1_relat_1 @ X16))),
% 3.11/3.35      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.11/3.35  thf('104', plain,
% 3.11/3.35      (![X31 : $i, X32 : $i]:
% 3.11/3.35         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 3.11/3.35          | (m1_subset_1 @ X31 @ 
% 3.11/3.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ X32)))
% 3.11/3.35          | ~ (v1_funct_1 @ X31)
% 3.11/3.35          | ~ (v1_relat_1 @ X31))),
% 3.11/3.35      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.11/3.35  thf('105', plain,
% 3.11/3.35      (![X0 : $i, X1 : $i]:
% 3.11/3.35         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.11/3.35          | ~ (v1_relat_1 @ X0)
% 3.11/3.35          | ~ (v1_funct_1 @ X0)
% 3.11/3.35          | ~ (v2_funct_1 @ X0)
% 3.11/3.35          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.11/3.35          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.11/3.35          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.11/3.35             (k1_zfmisc_1 @ 
% 3.11/3.35              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['103', '104'])).
% 3.11/3.35  thf('106', plain,
% 3.11/3.35      ((![X0 : $i]:
% 3.11/3.35          (~ (r1_tarski @ sk_A_1 @ X0)
% 3.11/3.35           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35              (k1_zfmisc_1 @ 
% 3.11/3.35               (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.11/3.35           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.11/3.35           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.11/3.35           | ~ (v2_funct_1 @ sk_C)
% 3.11/3.35           | ~ (v1_funct_1 @ sk_C)
% 3.11/3.35           | ~ (v1_relat_1 @ sk_C)))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['102', '105'])).
% 3.11/3.35  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 3.11/3.35      inference('demod', [status(thm)], ['4', '5'])).
% 3.11/3.35  thf('110', plain,
% 3.11/3.35      ((![X0 : $i]:
% 3.11/3.35          (~ (r1_tarski @ sk_A_1 @ X0)
% 3.11/3.35           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35              (k1_zfmisc_1 @ 
% 3.11/3.35               (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.11/3.35           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.11/3.35           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 3.11/3.35         <= (~
% 3.11/3.35             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 3.11/3.35      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 3.11/3.35  thf('111', plain,
% 3.11/3.35      (~
% 3.11/3.35       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 3.11/3.35      inference('sat_resolution*', [status(thm)], ['12', '86', '87'])).
% 3.11/3.35  thf('112', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (r1_tarski @ sk_A_1 @ X0)
% 3.11/3.35          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35             (k1_zfmisc_1 @ 
% 3.11/3.35              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.11/3.35          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.11/3.35          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.11/3.35      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 3.11/3.35  thf('113', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v1_relat_1 @ sk_C)
% 3.11/3.35          | ~ (v1_funct_1 @ sk_C)
% 3.11/3.35          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.11/3.35          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35             (k1_zfmisc_1 @ 
% 3.11/3.35              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.11/3.35          | ~ (r1_tarski @ sk_A_1 @ X0))),
% 3.11/3.35      inference('sup-', [status(thm)], ['93', '112'])).
% 3.11/3.35  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 3.11/3.35      inference('demod', [status(thm)], ['4', '5'])).
% 3.11/3.35  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('116', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.11/3.35          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35             (k1_zfmisc_1 @ 
% 3.11/3.35              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.11/3.35          | ~ (r1_tarski @ sk_A_1 @ X0))),
% 3.11/3.35      inference('demod', [status(thm)], ['113', '114', '115'])).
% 3.11/3.35  thf('117', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (v1_relat_1 @ sk_C)
% 3.11/3.35          | ~ (v1_funct_1 @ sk_C)
% 3.11/3.35          | ~ (r1_tarski @ sk_A_1 @ X0)
% 3.11/3.35          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35             (k1_zfmisc_1 @ 
% 3.11/3.35              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 3.11/3.35      inference('sup-', [status(thm)], ['92', '116'])).
% 3.11/3.35  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 3.11/3.35      inference('demod', [status(thm)], ['4', '5'])).
% 3.11/3.35  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('120', plain,
% 3.11/3.35      (![X0 : $i]:
% 3.11/3.35         (~ (r1_tarski @ sk_A_1 @ X0)
% 3.11/3.35          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35             (k1_zfmisc_1 @ 
% 3.11/3.35              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 3.11/3.35      inference('demod', [status(thm)], ['117', '118', '119'])).
% 3.11/3.35  thf('121', plain,
% 3.11/3.35      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35        (k1_zfmisc_1 @ 
% 3.11/3.35         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A_1)))),
% 3.11/3.35      inference('sup-', [status(thm)], ['91', '120'])).
% 3.11/3.35  thf('122', plain,
% 3.11/3.35      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A_1)))
% 3.11/3.35        | ~ (v1_relat_1 @ sk_C)
% 3.11/3.35        | ~ (v1_funct_1 @ sk_C)
% 3.11/3.35        | ~ (v2_funct_1 @ sk_C))),
% 3.11/3.35      inference('sup+', [status(thm)], ['90', '121'])).
% 3.11/3.35  thf('123', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.11/3.35      inference('sup+', [status(thm)], ['16', '17'])).
% 3.11/3.35  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 3.11/3.35      inference('demod', [status(thm)], ['4', '5'])).
% 3.11/3.35  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 3.11/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.11/3.35  thf('127', plain,
% 3.11/3.35      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.11/3.35        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 3.11/3.35      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 3.11/3.35  thf('128', plain, ($false), inference('demod', [status(thm)], ['89', '127'])).
% 3.11/3.35  
% 3.11/3.35  % SZS output end Refutation
% 3.11/3.35  
% 3.11/3.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
