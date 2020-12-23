%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3HVMxYdXQW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:39 EST 2020

% Result     : Theorem 3.72s
% Output     : Refutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 494 expanded)
%              Number of leaves         :   36 ( 157 expanded)
%              Depth                    :   27
%              Number of atoms          : 1392 (7632 expanded)
%              Number of equality atoms :   68 ( 318 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,(
    ! [X25: $i] :
      ( zip_tseitin_0 @ X25 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('64',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','83'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','84','85'])).

thf('87',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('88',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('89',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('90',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('91',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('96',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('98',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('100',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','84','85'])).

thf('102',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ X34 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
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

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','118'])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['87','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3HVMxYdXQW
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.72/3.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.72/3.93  % Solved by: fo/fo7.sh
% 3.72/3.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.72/3.93  % done 3389 iterations in 3.471s
% 3.72/3.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.72/3.93  % SZS output start Refutation
% 3.72/3.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.72/3.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.72/3.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.72/3.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.72/3.93  thf(sk_C_type, type, sk_C: $i).
% 3.72/3.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.72/3.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.72/3.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.72/3.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.72/3.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.72/3.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.72/3.93  thf(sk_A_type, type, sk_A: $i).
% 3.72/3.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.72/3.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.72/3.93  thf(sk_B_type, type, sk_B: $i).
% 3.72/3.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.72/3.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.72/3.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.72/3.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.72/3.93  thf(t31_funct_2, conjecture,
% 3.72/3.93    (![A:$i,B:$i,C:$i]:
% 3.72/3.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.72/3.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.72/3.93       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.72/3.93         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.72/3.93           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.72/3.93           ( m1_subset_1 @
% 3.72/3.93             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.72/3.93  thf(zf_stmt_0, negated_conjecture,
% 3.72/3.93    (~( ![A:$i,B:$i,C:$i]:
% 3.72/3.93        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.72/3.93            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.72/3.93          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.72/3.93            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.72/3.93              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.72/3.93              ( m1_subset_1 @
% 3.72/3.93                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 3.72/3.93    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 3.72/3.93  thf('0', plain,
% 3.72/3.93      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.72/3.93        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.72/3.93        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('1', plain,
% 3.72/3.93      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.72/3.93         <= (~
% 3.72/3.93             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.72/3.93      inference('split', [status(esa)], ['0'])).
% 3.72/3.93  thf('2', plain,
% 3.72/3.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf(cc1_relset_1, axiom,
% 3.72/3.93    (![A:$i,B:$i,C:$i]:
% 3.72/3.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.72/3.93       ( v1_relat_1 @ C ) ))).
% 3.72/3.93  thf('3', plain,
% 3.72/3.93      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.72/3.93         ((v1_relat_1 @ X16)
% 3.72/3.93          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.72/3.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.72/3.93  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 3.72/3.93      inference('sup-', [status(thm)], ['2', '3'])).
% 3.72/3.93  thf(dt_k2_funct_1, axiom,
% 3.72/3.93    (![A:$i]:
% 3.72/3.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.72/3.93       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.72/3.93         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.72/3.93  thf('5', plain,
% 3.72/3.93      (![X14 : $i]:
% 3.72/3.93         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 3.72/3.93          | ~ (v1_funct_1 @ X14)
% 3.72/3.93          | ~ (v1_relat_1 @ X14))),
% 3.72/3.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.72/3.93  thf('6', plain,
% 3.72/3.93      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.72/3.93         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.72/3.93      inference('split', [status(esa)], ['0'])).
% 3.72/3.93  thf('7', plain,
% 3.72/3.93      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 3.72/3.93         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['5', '6'])).
% 3.72/3.93  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('9', plain,
% 3.72/3.93      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.72/3.93      inference('demod', [status(thm)], ['7', '8'])).
% 3.72/3.93  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['4', '9'])).
% 3.72/3.93  thf('11', plain,
% 3.72/3.93      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('split', [status(esa)], ['0'])).
% 3.72/3.93  thf('12', plain,
% 3.72/3.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf(redefinition_k2_relset_1, axiom,
% 3.72/3.93    (![A:$i,B:$i,C:$i]:
% 3.72/3.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.72/3.93       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.72/3.93  thf('13', plain,
% 3.72/3.93      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.72/3.93         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 3.72/3.93          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.72/3.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.72/3.93  thf('14', plain,
% 3.72/3.93      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.72/3.93      inference('sup-', [status(thm)], ['12', '13'])).
% 3.72/3.93  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.72/3.93      inference('sup+', [status(thm)], ['14', '15'])).
% 3.72/3.93  thf(d1_funct_2, axiom,
% 3.72/3.93    (![A:$i,B:$i,C:$i]:
% 3.72/3.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.72/3.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.72/3.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.72/3.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.72/3.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.72/3.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.72/3.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.72/3.93  thf(zf_stmt_1, axiom,
% 3.72/3.93    (![B:$i,A:$i]:
% 3.72/3.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.72/3.93       ( zip_tseitin_0 @ B @ A ) ))).
% 3.72/3.93  thf('17', plain,
% 3.72/3.93      (![X25 : $i, X26 : $i]:
% 3.72/3.93         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.72/3.93  thf('18', plain,
% 3.72/3.93      (![X14 : $i]:
% 3.72/3.93         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 3.72/3.93          | ~ (v1_funct_1 @ X14)
% 3.72/3.93          | ~ (v1_relat_1 @ X14))),
% 3.72/3.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.72/3.93  thf(t55_funct_1, axiom,
% 3.72/3.93    (![A:$i]:
% 3.72/3.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.72/3.93       ( ( v2_funct_1 @ A ) =>
% 3.72/3.93         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.72/3.93           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.72/3.93  thf('19', plain,
% 3.72/3.93      (![X15 : $i]:
% 3.72/3.93         (~ (v2_funct_1 @ X15)
% 3.72/3.93          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 3.72/3.93          | ~ (v1_funct_1 @ X15)
% 3.72/3.93          | ~ (v1_relat_1 @ X15))),
% 3.72/3.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.72/3.93  thf(t64_relat_1, axiom,
% 3.72/3.93    (![A:$i]:
% 3.72/3.93     ( ( v1_relat_1 @ A ) =>
% 3.72/3.93       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 3.72/3.93           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.72/3.93         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.72/3.93  thf('20', plain,
% 3.72/3.93      (![X11 : $i]:
% 3.72/3.93         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 3.72/3.93          | ((X11) = (k1_xboole_0))
% 3.72/3.93          | ~ (v1_relat_1 @ X11))),
% 3.72/3.93      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.72/3.93  thf('21', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.72/3.93          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['19', '20'])).
% 3.72/3.93  thf('22', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['18', '21'])).
% 3.72/3.93  thf('23', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0))),
% 3.72/3.93      inference('simplify', [status(thm)], ['22'])).
% 3.72/3.93  thf('24', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.72/3.93         (((k2_relat_1 @ X1) != (X0))
% 3.72/3.93          | (zip_tseitin_0 @ X0 @ X2)
% 3.72/3.93          | ~ (v1_relat_1 @ X1)
% 3.72/3.93          | ~ (v1_funct_1 @ X1)
% 3.72/3.93          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.72/3.93          | ~ (v2_funct_1 @ X1))),
% 3.72/3.93      inference('sup-', [status(thm)], ['17', '23'])).
% 3.72/3.93  thf('25', plain,
% 3.72/3.93      (![X1 : $i, X2 : $i]:
% 3.72/3.93         (~ (v2_funct_1 @ X1)
% 3.72/3.93          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 3.72/3.93          | ~ (v1_funct_1 @ X1)
% 3.72/3.93          | ~ (v1_relat_1 @ X1)
% 3.72/3.93          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 3.72/3.93      inference('simplify', [status(thm)], ['24'])).
% 3.72/3.93  thf('26', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((zip_tseitin_0 @ sk_B @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ sk_C)
% 3.72/3.93          | ~ (v1_funct_1 @ sk_C)
% 3.72/3.93          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 3.72/3.93          | ~ (v2_funct_1 @ sk_C))),
% 3.72/3.93      inference('sup+', [status(thm)], ['16', '25'])).
% 3.72/3.93  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 3.72/3.93      inference('sup-', [status(thm)], ['2', '3'])).
% 3.72/3.93  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('30', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 3.72/3.93      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.72/3.93  thf('31', plain,
% 3.72/3.93      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('split', [status(esa)], ['0'])).
% 3.72/3.93  thf('32', plain,
% 3.72/3.93      ((![X0 : $i]:
% 3.72/3.93          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 3.72/3.93           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['30', '31'])).
% 3.72/3.93  thf('33', plain,
% 3.72/3.93      (![X25 : $i, X26 : $i]:
% 3.72/3.93         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.72/3.93  thf(t4_subset_1, axiom,
% 3.72/3.93    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.72/3.93  thf('34', plain,
% 3.72/3.93      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.72/3.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.72/3.93  thf(redefinition_k1_relset_1, axiom,
% 3.72/3.93    (![A:$i,B:$i,C:$i]:
% 3.72/3.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.72/3.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.72/3.93  thf('35', plain,
% 3.72/3.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.72/3.93         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 3.72/3.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.72/3.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.72/3.93  thf('36', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i]:
% 3.72/3.93         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.72/3.93      inference('sup-', [status(thm)], ['34', '35'])).
% 3.72/3.93  thf(t60_relat_1, axiom,
% 3.72/3.93    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.72/3.93     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.72/3.93  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.72/3.93      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.72/3.93  thf('38', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i]:
% 3.72/3.93         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.72/3.93      inference('demod', [status(thm)], ['36', '37'])).
% 3.72/3.93  thf(zf_stmt_2, axiom,
% 3.72/3.93    (![C:$i,B:$i,A:$i]:
% 3.72/3.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.72/3.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.72/3.93  thf('39', plain,
% 3.72/3.93      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.72/3.93         (((X27) != (k1_relset_1 @ X27 @ X28 @ X29))
% 3.72/3.93          | (v1_funct_2 @ X29 @ X27 @ X28)
% 3.72/3.93          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.72/3.93  thf('40', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i]:
% 3.72/3.93         (((X1) != (k1_xboole_0))
% 3.72/3.93          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.72/3.93          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.72/3.93      inference('sup-', [status(thm)], ['38', '39'])).
% 3.72/3.93  thf('41', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.72/3.93          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.72/3.93      inference('simplify', [status(thm)], ['40'])).
% 3.72/3.93  thf('42', plain,
% 3.72/3.93      (![X25 : $i, X26 : $i]:
% 3.72/3.93         ((zip_tseitin_0 @ X25 @ X26) | ((X26) != (k1_xboole_0)))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.72/3.93  thf('43', plain, (![X25 : $i]: (zip_tseitin_0 @ X25 @ k1_xboole_0)),
% 3.72/3.93      inference('simplify', [status(thm)], ['42'])).
% 3.72/3.93  thf('44', plain,
% 3.72/3.93      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.72/3.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.72/3.93  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.72/3.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.72/3.93  thf(zf_stmt_5, axiom,
% 3.72/3.93    (![A:$i,B:$i,C:$i]:
% 3.72/3.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.72/3.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.72/3.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.72/3.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.72/3.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.72/3.93  thf('45', plain,
% 3.72/3.93      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.72/3.93         (~ (zip_tseitin_0 @ X30 @ X31)
% 3.72/3.93          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 3.72/3.93          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.72/3.93  thf('46', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i]:
% 3.72/3.93         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.72/3.93      inference('sup-', [status(thm)], ['44', '45'])).
% 3.72/3.93  thf('47', plain,
% 3.72/3.93      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.72/3.93      inference('sup-', [status(thm)], ['43', '46'])).
% 3.72/3.93  thf('48', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.72/3.93      inference('demod', [status(thm)], ['41', '47'])).
% 3.72/3.93  thf('49', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.72/3.93         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.72/3.93      inference('sup+', [status(thm)], ['33', '48'])).
% 3.72/3.93  thf('50', plain,
% 3.72/3.93      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('clc', [status(thm)], ['32', '49'])).
% 3.72/3.93  thf('51', plain,
% 3.72/3.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('52', plain,
% 3.72/3.93      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.72/3.93         (~ (zip_tseitin_0 @ X30 @ X31)
% 3.72/3.93          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 3.72/3.93          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.72/3.93  thf('53', plain,
% 3.72/3.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.72/3.93      inference('sup-', [status(thm)], ['51', '52'])).
% 3.72/3.93  thf('54', plain,
% 3.72/3.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['50', '53'])).
% 3.72/3.93  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('56', plain,
% 3.72/3.93      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.72/3.93         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 3.72/3.93          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 3.72/3.93          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.72/3.93  thf('57', plain,
% 3.72/3.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 3.72/3.93        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['55', '56'])).
% 3.72/3.93  thf('58', plain,
% 3.72/3.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('59', plain,
% 3.72/3.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.72/3.93         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 3.72/3.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.72/3.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.72/3.93  thf('60', plain,
% 3.72/3.93      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 3.72/3.93      inference('sup-', [status(thm)], ['58', '59'])).
% 3.72/3.93  thf('61', plain,
% 3.72/3.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.72/3.93      inference('demod', [status(thm)], ['57', '60'])).
% 3.72/3.93  thf('62', plain,
% 3.72/3.93      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['54', '61'])).
% 3.72/3.93  thf('63', plain,
% 3.72/3.93      (![X15 : $i]:
% 3.72/3.93         (~ (v2_funct_1 @ X15)
% 3.72/3.93          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 3.72/3.93          | ~ (v1_funct_1 @ X15)
% 3.72/3.93          | ~ (v1_relat_1 @ X15))),
% 3.72/3.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.72/3.93  thf('64', plain,
% 3.72/3.93      (![X14 : $i]:
% 3.72/3.93         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 3.72/3.93          | ~ (v1_funct_1 @ X14)
% 3.72/3.93          | ~ (v1_relat_1 @ X14))),
% 3.72/3.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.72/3.93  thf('65', plain,
% 3.72/3.93      (![X14 : $i]:
% 3.72/3.93         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 3.72/3.93          | ~ (v1_funct_1 @ X14)
% 3.72/3.93          | ~ (v1_relat_1 @ X14))),
% 3.72/3.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.72/3.93  thf('66', plain,
% 3.72/3.93      (![X15 : $i]:
% 3.72/3.93         (~ (v2_funct_1 @ X15)
% 3.72/3.93          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 3.72/3.93          | ~ (v1_funct_1 @ X15)
% 3.72/3.93          | ~ (v1_relat_1 @ X15))),
% 3.72/3.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.72/3.93  thf(d10_xboole_0, axiom,
% 3.72/3.93    (![A:$i,B:$i]:
% 3.72/3.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.72/3.93  thf('67', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.72/3.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.72/3.93  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.72/3.93      inference('simplify', [status(thm)], ['67'])).
% 3.72/3.93  thf(t4_funct_2, axiom,
% 3.72/3.93    (![A:$i,B:$i]:
% 3.72/3.93     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.72/3.93       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.72/3.93         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.72/3.93           ( m1_subset_1 @
% 3.72/3.93             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.72/3.93  thf('69', plain,
% 3.72/3.93      (![X33 : $i, X34 : $i]:
% 3.72/3.93         (~ (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 3.72/3.93          | (v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ X34)
% 3.72/3.93          | ~ (v1_funct_1 @ X33)
% 3.72/3.93          | ~ (v1_relat_1 @ X33))),
% 3.72/3.93      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.72/3.93  thf('70', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['68', '69'])).
% 3.72/3.93  thf('71', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.72/3.93           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.72/3.93      inference('sup+', [status(thm)], ['66', '70'])).
% 3.72/3.93  thf('72', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.72/3.93             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['65', '71'])).
% 3.72/3.93  thf('73', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.72/3.93           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0))),
% 3.72/3.93      inference('simplify', [status(thm)], ['72'])).
% 3.72/3.93  thf('74', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.72/3.93             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['64', '73'])).
% 3.72/3.93  thf('75', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.72/3.93           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0))),
% 3.72/3.93      inference('simplify', [status(thm)], ['74'])).
% 3.72/3.93  thf('76', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.72/3.93           (k1_relat_1 @ X0))
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v2_funct_1 @ X0))),
% 3.72/3.93      inference('sup+', [status(thm)], ['63', '75'])).
% 3.72/3.93  thf('77', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.72/3.93             (k1_relat_1 @ X0)))),
% 3.72/3.93      inference('simplify', [status(thm)], ['76'])).
% 3.72/3.93  thf('78', plain,
% 3.72/3.93      ((((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 3.72/3.93         | ~ (v1_relat_1 @ sk_C)
% 3.72/3.93         | ~ (v1_funct_1 @ sk_C)
% 3.72/3.93         | ~ (v2_funct_1 @ sk_C)))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('sup+', [status(thm)], ['62', '77'])).
% 3.72/3.93  thf('79', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.72/3.93      inference('sup+', [status(thm)], ['14', '15'])).
% 3.72/3.93  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 3.72/3.93      inference('sup-', [status(thm)], ['2', '3'])).
% 3.72/3.93  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('83', plain,
% 3.72/3.93      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 3.72/3.93         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 3.72/3.93      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 3.72/3.93  thf('84', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 3.72/3.93      inference('demod', [status(thm)], ['11', '83'])).
% 3.72/3.93  thf('85', plain,
% 3.72/3.93      (~
% 3.72/3.93       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 3.72/3.93       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 3.72/3.93       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.72/3.93      inference('split', [status(esa)], ['0'])).
% 3.72/3.93  thf('86', plain,
% 3.72/3.93      (~
% 3.72/3.93       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.72/3.93      inference('sat_resolution*', [status(thm)], ['10', '84', '85'])).
% 3.72/3.93  thf('87', plain,
% 3.72/3.93      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.72/3.93      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 3.72/3.93  thf('88', plain,
% 3.72/3.93      (![X15 : $i]:
% 3.72/3.93         (~ (v2_funct_1 @ X15)
% 3.72/3.93          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 3.72/3.93          | ~ (v1_funct_1 @ X15)
% 3.72/3.93          | ~ (v1_relat_1 @ X15))),
% 3.72/3.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.72/3.93  thf('89', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.72/3.93      inference('simplify', [status(thm)], ['67'])).
% 3.72/3.93  thf('90', plain,
% 3.72/3.93      (![X14 : $i]:
% 3.72/3.93         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 3.72/3.93          | ~ (v1_funct_1 @ X14)
% 3.72/3.93          | ~ (v1_relat_1 @ X14))),
% 3.72/3.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.72/3.93  thf('91', plain,
% 3.72/3.93      (![X14 : $i]:
% 3.72/3.93         ((v1_funct_1 @ (k2_funct_1 @ X14))
% 3.72/3.93          | ~ (v1_funct_1 @ X14)
% 3.72/3.93          | ~ (v1_relat_1 @ X14))),
% 3.72/3.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.72/3.93  thf('92', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 3.72/3.93      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.72/3.93  thf('93', plain,
% 3.72/3.93      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.72/3.93         <= (~
% 3.72/3.93             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.72/3.93      inference('split', [status(esa)], ['0'])).
% 3.72/3.93  thf('94', plain,
% 3.72/3.93      ((![X0 : $i]:
% 3.72/3.93          (~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.72/3.93              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.72/3.93           | (zip_tseitin_0 @ sk_B @ X0)))
% 3.72/3.93         <= (~
% 3.72/3.93             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['92', '93'])).
% 3.72/3.93  thf('95', plain,
% 3.72/3.93      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.72/3.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.72/3.93  thf('96', plain,
% 3.72/3.93      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.72/3.93         <= (~
% 3.72/3.93             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.72/3.93      inference('demod', [status(thm)], ['94', '95'])).
% 3.72/3.93  thf('97', plain,
% 3.72/3.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.72/3.93      inference('sup-', [status(thm)], ['51', '52'])).
% 3.72/3.93  thf('98', plain,
% 3.72/3.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 3.72/3.93         <= (~
% 3.72/3.93             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['96', '97'])).
% 3.72/3.93  thf('99', plain,
% 3.72/3.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 3.72/3.93      inference('demod', [status(thm)], ['57', '60'])).
% 3.72/3.93  thf('100', plain,
% 3.72/3.93      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 3.72/3.93         <= (~
% 3.72/3.93             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['98', '99'])).
% 3.72/3.93  thf('101', plain,
% 3.72/3.93      (~
% 3.72/3.93       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.72/3.93      inference('sat_resolution*', [status(thm)], ['10', '84', '85'])).
% 3.72/3.93  thf('102', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 3.72/3.93      inference('simpl_trail', [status(thm)], ['100', '101'])).
% 3.72/3.93  thf('103', plain,
% 3.72/3.93      (![X15 : $i]:
% 3.72/3.93         (~ (v2_funct_1 @ X15)
% 3.72/3.93          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 3.72/3.93          | ~ (v1_funct_1 @ X15)
% 3.72/3.93          | ~ (v1_relat_1 @ X15))),
% 3.72/3.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.72/3.93  thf('104', plain,
% 3.72/3.93      (![X33 : $i, X34 : $i]:
% 3.72/3.93         (~ (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 3.72/3.93          | (m1_subset_1 @ X33 @ 
% 3.72/3.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ X34)))
% 3.72/3.93          | ~ (v1_funct_1 @ X33)
% 3.72/3.93          | ~ (v1_relat_1 @ X33))),
% 3.72/3.93      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.72/3.93  thf('105', plain,
% 3.72/3.93      (![X0 : $i, X1 : $i]:
% 3.72/3.93         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.72/3.93          | ~ (v1_relat_1 @ X0)
% 3.72/3.93          | ~ (v1_funct_1 @ X0)
% 3.72/3.93          | ~ (v2_funct_1 @ X0)
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.72/3.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.72/3.93          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.72/3.93             (k1_zfmisc_1 @ 
% 3.72/3.93              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['103', '104'])).
% 3.72/3.93  thf('106', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (r1_tarski @ sk_A @ X0)
% 3.72/3.93          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93             (k1_zfmisc_1 @ 
% 3.72/3.93              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.72/3.93          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.72/3.93          | ~ (v2_funct_1 @ sk_C)
% 3.72/3.93          | ~ (v1_funct_1 @ sk_C)
% 3.72/3.93          | ~ (v1_relat_1 @ sk_C))),
% 3.72/3.93      inference('sup-', [status(thm)], ['102', '105'])).
% 3.72/3.93  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 3.72/3.93      inference('sup-', [status(thm)], ['2', '3'])).
% 3.72/3.93  thf('110', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (r1_tarski @ sk_A @ X0)
% 3.72/3.93          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93             (k1_zfmisc_1 @ 
% 3.72/3.93              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.72/3.93          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.72/3.93      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 3.72/3.93  thf('111', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v1_relat_1 @ sk_C)
% 3.72/3.93          | ~ (v1_funct_1 @ sk_C)
% 3.72/3.93          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.72/3.93          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93             (k1_zfmisc_1 @ 
% 3.72/3.93              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.72/3.93          | ~ (r1_tarski @ sk_A @ X0))),
% 3.72/3.93      inference('sup-', [status(thm)], ['91', '110'])).
% 3.72/3.93  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 3.72/3.93      inference('sup-', [status(thm)], ['2', '3'])).
% 3.72/3.93  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('114', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.72/3.93          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93             (k1_zfmisc_1 @ 
% 3.72/3.93              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 3.72/3.93          | ~ (r1_tarski @ sk_A @ X0))),
% 3.72/3.93      inference('demod', [status(thm)], ['111', '112', '113'])).
% 3.72/3.93  thf('115', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (v1_relat_1 @ sk_C)
% 3.72/3.93          | ~ (v1_funct_1 @ sk_C)
% 3.72/3.93          | ~ (r1_tarski @ sk_A @ X0)
% 3.72/3.93          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93             (k1_zfmisc_1 @ 
% 3.72/3.93              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 3.72/3.93      inference('sup-', [status(thm)], ['90', '114'])).
% 3.72/3.93  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 3.72/3.93      inference('sup-', [status(thm)], ['2', '3'])).
% 3.72/3.93  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('118', plain,
% 3.72/3.93      (![X0 : $i]:
% 3.72/3.93         (~ (r1_tarski @ sk_A @ X0)
% 3.72/3.93          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93             (k1_zfmisc_1 @ 
% 3.72/3.93              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))))),
% 3.72/3.93      inference('demod', [status(thm)], ['115', '116', '117'])).
% 3.72/3.93  thf('119', plain,
% 3.72/3.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93        (k1_zfmisc_1 @ 
% 3.72/3.93         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 3.72/3.93      inference('sup-', [status(thm)], ['89', '118'])).
% 3.72/3.93  thf('120', plain,
% 3.72/3.93      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 3.72/3.93        | ~ (v1_relat_1 @ sk_C)
% 3.72/3.93        | ~ (v1_funct_1 @ sk_C)
% 3.72/3.93        | ~ (v2_funct_1 @ sk_C))),
% 3.72/3.93      inference('sup+', [status(thm)], ['88', '119'])).
% 3.72/3.93  thf('121', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.72/3.93      inference('sup+', [status(thm)], ['14', '15'])).
% 3.72/3.93  thf('122', plain, ((v1_relat_1 @ sk_C)),
% 3.72/3.93      inference('sup-', [status(thm)], ['2', '3'])).
% 3.72/3.93  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('124', plain, ((v2_funct_1 @ sk_C)),
% 3.72/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.72/3.93  thf('125', plain,
% 3.72/3.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.72/3.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.72/3.93      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 3.72/3.93  thf('126', plain, ($false), inference('demod', [status(thm)], ['87', '125'])).
% 3.72/3.93  
% 3.72/3.93  % SZS output end Refutation
% 3.72/3.93  
% 3.72/3.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
