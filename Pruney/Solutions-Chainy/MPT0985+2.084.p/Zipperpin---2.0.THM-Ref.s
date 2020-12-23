%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nRZ9xGz3dK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:38 EST 2020

% Result     : Theorem 4.51s
% Output     : Refutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 708 expanded)
%              Number of leaves         :   50 ( 234 expanded)
%              Depth                    :   23
%              Number of atoms          : 1825 (10049 expanded)
%              Number of equality atoms :  103 ( 460 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('34',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('41',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('42',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','44'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','44'])).

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

thf('53',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['32','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('76',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('77',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( v1_funct_2 @ X37 @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['74','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['73','97'])).

thf('99',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','99','100'])).

thf('102',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','101'])).

thf('103',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('104',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','44'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('111',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('113',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('118',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('120',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('122',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('126',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('127',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['125','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('133',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('134',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('135',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('138',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('139',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('140',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('143',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('144',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('145',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('147',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['143','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['124','157','158','159','160'])).

thf('162',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','99','100'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','171'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['102','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nRZ9xGz3dK
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.51/4.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.51/4.68  % Solved by: fo/fo7.sh
% 4.51/4.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.51/4.68  % done 4068 iterations in 4.232s
% 4.51/4.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.51/4.68  % SZS output start Refutation
% 4.51/4.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.51/4.68  thf(sk_A_type, type, sk_A: $i).
% 4.51/4.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.51/4.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.51/4.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.51/4.68  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.51/4.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.51/4.68  thf(sk_C_type, type, sk_C: $i).
% 4.51/4.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.51/4.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.51/4.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.51/4.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.51/4.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.51/4.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.51/4.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.51/4.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.51/4.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.51/4.68  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 4.51/4.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.51/4.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.51/4.68  thf(sk_B_type, type, sk_B: $i).
% 4.51/4.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.51/4.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.51/4.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.51/4.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.51/4.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.51/4.68  thf(t31_funct_2, conjecture,
% 4.51/4.68    (![A:$i,B:$i,C:$i]:
% 4.51/4.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.51/4.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.51/4.68       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.51/4.68         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.51/4.68           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.51/4.68           ( m1_subset_1 @
% 4.51/4.68             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.51/4.68  thf(zf_stmt_0, negated_conjecture,
% 4.51/4.68    (~( ![A:$i,B:$i,C:$i]:
% 4.51/4.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.51/4.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.51/4.68          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.51/4.68            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.51/4.68              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.51/4.68              ( m1_subset_1 @
% 4.51/4.68                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 4.51/4.68    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 4.51/4.68  thf('0', plain,
% 4.51/4.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.51/4.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 4.51/4.68        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('1', plain,
% 4.51/4.68      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('split', [status(esa)], ['0'])).
% 4.51/4.68  thf('2', plain,
% 4.51/4.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf(cc1_relset_1, axiom,
% 4.51/4.68    (![A:$i,B:$i,C:$i]:
% 4.51/4.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.51/4.68       ( v1_relat_1 @ C ) ))).
% 4.51/4.68  thf('3', plain,
% 4.51/4.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.51/4.68         ((v1_relat_1 @ X17)
% 4.51/4.68          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.51/4.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.51/4.68  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf(dt_k2_funct_1, axiom,
% 4.51/4.68    (![A:$i]:
% 4.51/4.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.51/4.68       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.51/4.68         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.51/4.68  thf('5', plain,
% 4.51/4.68      (![X12 : $i]:
% 4.51/4.68         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 4.51/4.68          | ~ (v1_funct_1 @ X12)
% 4.51/4.68          | ~ (v1_relat_1 @ X12))),
% 4.51/4.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.51/4.68  thf('6', plain,
% 4.51/4.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.51/4.68         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.51/4.68      inference('split', [status(esa)], ['0'])).
% 4.51/4.68  thf('7', plain,
% 4.51/4.68      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 4.51/4.68         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['5', '6'])).
% 4.51/4.68  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('9', plain,
% 4.51/4.68      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.51/4.68      inference('demod', [status(thm)], ['7', '8'])).
% 4.51/4.68  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['4', '9'])).
% 4.51/4.68  thf('11', plain,
% 4.51/4.68      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.51/4.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.51/4.68      inference('split', [status(esa)], ['0'])).
% 4.51/4.68  thf('12', plain,
% 4.51/4.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf(redefinition_k2_relset_1, axiom,
% 4.51/4.68    (![A:$i,B:$i,C:$i]:
% 4.51/4.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.51/4.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.51/4.68  thf('13', plain,
% 4.51/4.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.51/4.68         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 4.51/4.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.51/4.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.51/4.68  thf('14', plain,
% 4.51/4.68      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.51/4.68      inference('sup-', [status(thm)], ['12', '13'])).
% 4.51/4.68  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.51/4.68      inference('sup+', [status(thm)], ['14', '15'])).
% 4.51/4.68  thf(d1_funct_2, axiom,
% 4.51/4.68    (![A:$i,B:$i,C:$i]:
% 4.51/4.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.51/4.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.51/4.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.51/4.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.51/4.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.51/4.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.51/4.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.51/4.68  thf(zf_stmt_1, axiom,
% 4.51/4.68    (![B:$i,A:$i]:
% 4.51/4.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.51/4.68       ( zip_tseitin_0 @ B @ A ) ))).
% 4.51/4.68  thf('17', plain,
% 4.51/4.68      (![X29 : $i, X30 : $i]:
% 4.51/4.68         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.51/4.68  thf('18', plain,
% 4.51/4.68      (![X12 : $i]:
% 4.51/4.68         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 4.51/4.68          | ~ (v1_funct_1 @ X12)
% 4.51/4.68          | ~ (v1_relat_1 @ X12))),
% 4.51/4.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.51/4.68  thf(t55_funct_1, axiom,
% 4.51/4.68    (![A:$i]:
% 4.51/4.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.51/4.68       ( ( v2_funct_1 @ A ) =>
% 4.51/4.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.51/4.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.51/4.68  thf('19', plain,
% 4.51/4.68      (![X15 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X15)
% 4.51/4.68          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 4.51/4.68          | ~ (v1_funct_1 @ X15)
% 4.51/4.68          | ~ (v1_relat_1 @ X15))),
% 4.51/4.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.51/4.68  thf(t64_relat_1, axiom,
% 4.51/4.68    (![A:$i]:
% 4.51/4.68     ( ( v1_relat_1 @ A ) =>
% 4.51/4.68       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 4.51/4.68           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.51/4.68         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 4.51/4.68  thf('20', plain,
% 4.51/4.68      (![X9 : $i]:
% 4.51/4.68         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 4.51/4.68          | ((X9) = (k1_xboole_0))
% 4.51/4.68          | ~ (v1_relat_1 @ X9))),
% 4.51/4.68      inference('cnf', [status(esa)], [t64_relat_1])).
% 4.51/4.68  thf('21', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.51/4.68          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['19', '20'])).
% 4.51/4.68  thf('22', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['18', '21'])).
% 4.51/4.68  thf('23', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0))),
% 4.51/4.68      inference('simplify', [status(thm)], ['22'])).
% 4.51/4.68  thf('24', plain,
% 4.51/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.51/4.68         (((k2_relat_1 @ X1) != (X0))
% 4.51/4.68          | (zip_tseitin_0 @ X0 @ X2)
% 4.51/4.68          | ~ (v1_relat_1 @ X1)
% 4.51/4.68          | ~ (v1_funct_1 @ X1)
% 4.51/4.68          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 4.51/4.68          | ~ (v2_funct_1 @ X1))),
% 4.51/4.68      inference('sup-', [status(thm)], ['17', '23'])).
% 4.51/4.68  thf('25', plain,
% 4.51/4.68      (![X1 : $i, X2 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X1)
% 4.51/4.68          | ((k2_funct_1 @ X1) = (k1_xboole_0))
% 4.51/4.68          | ~ (v1_funct_1 @ X1)
% 4.51/4.68          | ~ (v1_relat_1 @ X1)
% 4.51/4.68          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 4.51/4.68      inference('simplify', [status(thm)], ['24'])).
% 4.51/4.68  thf('26', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((zip_tseitin_0 @ sk_B @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ sk_C)
% 4.51/4.68          | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 4.51/4.68          | ~ (v2_funct_1 @ sk_C))),
% 4.51/4.68      inference('sup+', [status(thm)], ['16', '25'])).
% 4.51/4.68  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('30', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 4.51/4.68      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 4.51/4.68  thf('31', plain,
% 4.51/4.68      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.51/4.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.51/4.68      inference('split', [status(esa)], ['0'])).
% 4.51/4.68  thf('32', plain,
% 4.51/4.68      ((![X0 : $i]:
% 4.51/4.68          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 4.51/4.68           | (zip_tseitin_0 @ sk_B @ X0)))
% 4.51/4.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['30', '31'])).
% 4.51/4.68  thf('33', plain,
% 4.51/4.68      (![X29 : $i, X30 : $i]:
% 4.51/4.68         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.51/4.68  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 4.51/4.68  thf('34', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.51/4.68      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.51/4.68  thf(t71_relat_1, axiom,
% 4.51/4.68    (![A:$i]:
% 4.51/4.68     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.51/4.68       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.51/4.68  thf('35', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 4.51/4.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.51/4.68  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.51/4.68      inference('sup+', [status(thm)], ['34', '35'])).
% 4.51/4.68  thf(t4_funct_2, axiom,
% 4.51/4.68    (![A:$i,B:$i]:
% 4.51/4.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.51/4.68       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.51/4.68         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 4.51/4.68           ( m1_subset_1 @
% 4.51/4.68             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 4.51/4.68  thf('37', plain,
% 4.51/4.68      (![X37 : $i, X38 : $i]:
% 4.51/4.68         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 4.51/4.68          | (m1_subset_1 @ X37 @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ X38)))
% 4.51/4.68          | ~ (v1_funct_1 @ X37)
% 4.51/4.68          | ~ (v1_relat_1 @ X37))),
% 4.51/4.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.51/4.68  thf('38', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 4.51/4.68          | ~ (v1_funct_1 @ k1_xboole_0)
% 4.51/4.68          | (m1_subset_1 @ k1_xboole_0 @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X0))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['36', '37'])).
% 4.51/4.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.51/4.68  thf('39', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.51/4.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.51/4.68  thf(t45_ordinal1, axiom,
% 4.51/4.68    (![A:$i]:
% 4.51/4.68     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 4.51/4.68       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 4.51/4.68  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.51/4.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 4.51/4.68  thf('41', plain, ((v1_funct_1 @ k1_xboole_0)),
% 4.51/4.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 4.51/4.68  thf('42', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.51/4.68      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.51/4.68  thf('43', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 4.51/4.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.51/4.68  thf('44', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.51/4.68      inference('sup+', [status(thm)], ['42', '43'])).
% 4.51/4.68  thf('45', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (m1_subset_1 @ k1_xboole_0 @ 
% 4.51/4.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 4.51/4.68      inference('demod', [status(thm)], ['38', '39', '40', '41', '44'])).
% 4.51/4.68  thf(redefinition_k1_relset_1, axiom,
% 4.51/4.68    (![A:$i,B:$i,C:$i]:
% 4.51/4.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.51/4.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.51/4.68  thf('46', plain,
% 4.51/4.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.51/4.68         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 4.51/4.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.51/4.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.51/4.68  thf('47', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 4.51/4.68           = (k1_relat_1 @ k1_xboole_0))),
% 4.51/4.68      inference('sup-', [status(thm)], ['45', '46'])).
% 4.51/4.68  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.51/4.68      inference('sup+', [status(thm)], ['42', '43'])).
% 4.51/4.68  thf('49', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.51/4.68      inference('demod', [status(thm)], ['47', '48'])).
% 4.51/4.68  thf(zf_stmt_2, axiom,
% 4.51/4.68    (![C:$i,B:$i,A:$i]:
% 4.51/4.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.51/4.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.51/4.68  thf('50', plain,
% 4.51/4.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.51/4.68         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 4.51/4.68          | (v1_funct_2 @ X33 @ X31 @ X32)
% 4.51/4.68          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.51/4.68  thf('51', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (((k1_xboole_0) != (k1_xboole_0))
% 4.51/4.68          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 4.51/4.68          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 4.51/4.68      inference('sup-', [status(thm)], ['49', '50'])).
% 4.51/4.68  thf('52', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (m1_subset_1 @ k1_xboole_0 @ 
% 4.51/4.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 4.51/4.68      inference('demod', [status(thm)], ['38', '39', '40', '41', '44'])).
% 4.51/4.68  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.51/4.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.51/4.68  thf(zf_stmt_5, axiom,
% 4.51/4.68    (![A:$i,B:$i,C:$i]:
% 4.51/4.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.51/4.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.51/4.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.51/4.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.51/4.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.51/4.68  thf('53', plain,
% 4.51/4.68      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.51/4.68         (~ (zip_tseitin_0 @ X34 @ X35)
% 4.51/4.68          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 4.51/4.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.51/4.68  thf('54', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 4.51/4.68          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 4.51/4.68      inference('sup-', [status(thm)], ['52', '53'])).
% 4.51/4.68  thf('55', plain,
% 4.51/4.68      (![X29 : $i, X30 : $i]:
% 4.51/4.68         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.51/4.68  thf('56', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 4.51/4.68      inference('simplify', [status(thm)], ['55'])).
% 4.51/4.68  thf('57', plain,
% 4.51/4.68      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.51/4.68      inference('demod', [status(thm)], ['54', '56'])).
% 4.51/4.68  thf('58', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (((k1_xboole_0) != (k1_xboole_0))
% 4.51/4.68          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 4.51/4.68      inference('demod', [status(thm)], ['51', '57'])).
% 4.51/4.68  thf('59', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.51/4.68      inference('simplify', [status(thm)], ['58'])).
% 4.51/4.68  thf('60', plain,
% 4.51/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.51/4.68         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 4.51/4.68      inference('sup+', [status(thm)], ['33', '59'])).
% 4.51/4.68  thf('61', plain,
% 4.51/4.68      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 4.51/4.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.51/4.68      inference('clc', [status(thm)], ['32', '60'])).
% 4.51/4.68  thf('62', plain,
% 4.51/4.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('63', plain,
% 4.51/4.68      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.51/4.68         (~ (zip_tseitin_0 @ X34 @ X35)
% 4.51/4.68          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 4.51/4.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.51/4.68  thf('64', plain,
% 4.51/4.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.51/4.68      inference('sup-', [status(thm)], ['62', '63'])).
% 4.51/4.68  thf('65', plain,
% 4.51/4.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 4.51/4.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['61', '64'])).
% 4.51/4.68  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('67', plain,
% 4.51/4.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.51/4.68         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 4.51/4.68          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 4.51/4.68          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.51/4.68  thf('68', plain,
% 4.51/4.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 4.51/4.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['66', '67'])).
% 4.51/4.68  thf('69', plain,
% 4.51/4.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('70', plain,
% 4.51/4.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.51/4.68         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 4.51/4.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.51/4.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.51/4.68  thf('71', plain,
% 4.51/4.68      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 4.51/4.68      inference('sup-', [status(thm)], ['69', '70'])).
% 4.51/4.68  thf('72', plain,
% 4.51/4.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.51/4.68      inference('demod', [status(thm)], ['68', '71'])).
% 4.51/4.68  thf('73', plain,
% 4.51/4.68      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 4.51/4.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['65', '72'])).
% 4.51/4.68  thf('74', plain,
% 4.51/4.68      (![X15 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X15)
% 4.51/4.68          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 4.51/4.68          | ~ (v1_funct_1 @ X15)
% 4.51/4.68          | ~ (v1_relat_1 @ X15))),
% 4.51/4.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.51/4.68  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.51/4.68      inference('sup+', [status(thm)], ['14', '15'])).
% 4.51/4.68  thf('76', plain,
% 4.51/4.68      (![X12 : $i]:
% 4.51/4.68         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 4.51/4.68          | ~ (v1_funct_1 @ X12)
% 4.51/4.68          | ~ (v1_relat_1 @ X12))),
% 4.51/4.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.51/4.68  thf('77', plain,
% 4.51/4.68      (![X12 : $i]:
% 4.51/4.68         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 4.51/4.68          | ~ (v1_funct_1 @ X12)
% 4.51/4.68          | ~ (v1_relat_1 @ X12))),
% 4.51/4.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.51/4.68  thf('78', plain,
% 4.51/4.68      (![X15 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X15)
% 4.51/4.68          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 4.51/4.68          | ~ (v1_funct_1 @ X15)
% 4.51/4.68          | ~ (v1_relat_1 @ X15))),
% 4.51/4.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.51/4.68  thf(d10_xboole_0, axiom,
% 4.51/4.68    (![A:$i,B:$i]:
% 4.51/4.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.51/4.68  thf('79', plain,
% 4.51/4.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.51/4.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.51/4.68  thf('80', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.51/4.68      inference('simplify', [status(thm)], ['79'])).
% 4.51/4.68  thf('81', plain,
% 4.51/4.68      (![X37 : $i, X38 : $i]:
% 4.51/4.68         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 4.51/4.68          | (v1_funct_2 @ X37 @ (k1_relat_1 @ X37) @ X38)
% 4.51/4.68          | ~ (v1_funct_1 @ X37)
% 4.51/4.68          | ~ (v1_relat_1 @ X37))),
% 4.51/4.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.51/4.68  thf('82', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['80', '81'])).
% 4.51/4.68  thf('83', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.51/4.68           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.51/4.68      inference('sup+', [status(thm)], ['78', '82'])).
% 4.51/4.68  thf('84', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.51/4.68             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['77', '83'])).
% 4.51/4.68  thf('85', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.51/4.68           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0))),
% 4.51/4.68      inference('simplify', [status(thm)], ['84'])).
% 4.51/4.68  thf('86', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.51/4.68             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['76', '85'])).
% 4.51/4.68  thf('87', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.51/4.68           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0))),
% 4.51/4.68      inference('simplify', [status(thm)], ['86'])).
% 4.51/4.68  thf('88', plain,
% 4.51/4.68      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 4.51/4.68         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.51/4.68        | ~ (v1_relat_1 @ sk_C)
% 4.51/4.68        | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68        | ~ (v2_funct_1 @ sk_C))),
% 4.51/4.68      inference('sup+', [status(thm)], ['75', '87'])).
% 4.51/4.68  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('92', plain,
% 4.51/4.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 4.51/4.68        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.51/4.68      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 4.51/4.68  thf('93', plain,
% 4.51/4.68      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 4.51/4.68        | ~ (v1_relat_1 @ sk_C)
% 4.51/4.68        | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68        | ~ (v2_funct_1 @ sk_C))),
% 4.51/4.68      inference('sup+', [status(thm)], ['74', '92'])).
% 4.51/4.68  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('97', plain,
% 4.51/4.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 4.51/4.68      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 4.51/4.68  thf('98', plain,
% 4.51/4.68      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.51/4.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.51/4.68      inference('sup+', [status(thm)], ['73', '97'])).
% 4.51/4.68  thf('99', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 4.51/4.68      inference('demod', [status(thm)], ['11', '98'])).
% 4.51/4.68  thf('100', plain,
% 4.51/4.68      (~
% 4.51/4.68       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 4.51/4.68       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 4.51/4.68       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.51/4.68      inference('split', [status(esa)], ['0'])).
% 4.51/4.68  thf('101', plain,
% 4.51/4.68      (~
% 4.51/4.68       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.51/4.68      inference('sat_resolution*', [status(thm)], ['10', '99', '100'])).
% 4.51/4.68  thf('102', plain,
% 4.51/4.68      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.51/4.68      inference('simpl_trail', [status(thm)], ['1', '101'])).
% 4.51/4.68  thf('103', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.51/4.68      inference('simplify', [status(thm)], ['79'])).
% 4.51/4.68  thf('104', plain,
% 4.51/4.68      (![X12 : $i]:
% 4.51/4.68         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 4.51/4.68          | ~ (v1_funct_1 @ X12)
% 4.51/4.68          | ~ (v1_relat_1 @ X12))),
% 4.51/4.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.51/4.68  thf('105', plain,
% 4.51/4.68      (![X12 : $i]:
% 4.51/4.68         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 4.51/4.68          | ~ (v1_funct_1 @ X12)
% 4.51/4.68          | ~ (v1_relat_1 @ X12))),
% 4.51/4.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.51/4.68  thf('106', plain,
% 4.51/4.68      (![X29 : $i, X30 : $i]:
% 4.51/4.68         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.51/4.68  thf('107', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (m1_subset_1 @ k1_xboole_0 @ 
% 4.51/4.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 4.51/4.68      inference('demod', [status(thm)], ['38', '39', '40', '41', '44'])).
% 4.51/4.68  thf('108', plain,
% 4.51/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.51/4.68         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 4.51/4.68          | (zip_tseitin_0 @ X0 @ X2))),
% 4.51/4.68      inference('sup+', [status(thm)], ['106', '107'])).
% 4.51/4.68  thf('109', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 4.51/4.68      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 4.51/4.68  thf('110', plain,
% 4.51/4.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.51/4.68      inference('sup-', [status(thm)], ['62', '63'])).
% 4.51/4.68  thf('111', plain,
% 4.51/4.68      ((((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 4.51/4.68        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.51/4.68      inference('sup-', [status(thm)], ['109', '110'])).
% 4.51/4.68  thf('112', plain,
% 4.51/4.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.51/4.68      inference('demod', [status(thm)], ['68', '71'])).
% 4.51/4.68  thf('113', plain,
% 4.51/4.68      ((((k2_funct_1 @ sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['111', '112'])).
% 4.51/4.68  thf('114', plain,
% 4.51/4.68      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('split', [status(esa)], ['0'])).
% 4.51/4.68  thf('115', plain,
% 4.51/4.68      (((~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.51/4.68            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.51/4.68         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['113', '114'])).
% 4.51/4.68  thf('116', plain,
% 4.51/4.68      ((![X0 : $i]:
% 4.51/4.68          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['108', '115'])).
% 4.51/4.68  thf('117', plain,
% 4.51/4.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.51/4.68      inference('sup-', [status(thm)], ['62', '63'])).
% 4.51/4.68  thf('118', plain,
% 4.51/4.68      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['116', '117'])).
% 4.51/4.68  thf('119', plain,
% 4.51/4.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.51/4.68      inference('demod', [status(thm)], ['68', '71'])).
% 4.51/4.68  thf('120', plain,
% 4.51/4.68      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('clc', [status(thm)], ['118', '119'])).
% 4.51/4.68  thf('121', plain,
% 4.51/4.68      (![X15 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X15)
% 4.51/4.68          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 4.51/4.68          | ~ (v1_funct_1 @ X15)
% 4.51/4.68          | ~ (v1_relat_1 @ X15))),
% 4.51/4.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.51/4.68  thf('122', plain,
% 4.51/4.68      (![X37 : $i, X38 : $i]:
% 4.51/4.68         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 4.51/4.68          | (m1_subset_1 @ X37 @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ X38)))
% 4.51/4.68          | ~ (v1_funct_1 @ X37)
% 4.51/4.68          | ~ (v1_relat_1 @ X37))),
% 4.51/4.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.51/4.68  thf('123', plain,
% 4.51/4.68      (![X0 : $i, X1 : $i]:
% 4.51/4.68         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.51/4.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.51/4.68          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.51/4.68             (k1_zfmisc_1 @ 
% 4.51/4.68              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['121', '122'])).
% 4.51/4.68  thf('124', plain,
% 4.51/4.68      ((![X0 : $i]:
% 4.51/4.68          (~ (r1_tarski @ sk_A @ X0)
% 4.51/4.68           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68              (k1_zfmisc_1 @ 
% 4.51/4.68               (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 4.51/4.68           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.51/4.68           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.51/4.68           | ~ (v2_funct_1 @ sk_C)
% 4.51/4.68           | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68           | ~ (v1_relat_1 @ sk_C)))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['120', '123'])).
% 4.51/4.68  thf('125', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.51/4.68      inference('sup+', [status(thm)], ['14', '15'])).
% 4.51/4.68  thf('126', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.51/4.68      inference('simplify', [status(thm)], ['79'])).
% 4.51/4.68  thf('127', plain,
% 4.51/4.68      (![X37 : $i, X38 : $i]:
% 4.51/4.68         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 4.51/4.68          | (m1_subset_1 @ X37 @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ X38)))
% 4.51/4.68          | ~ (v1_funct_1 @ X37)
% 4.51/4.68          | ~ (v1_relat_1 @ X37))),
% 4.51/4.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.51/4.68  thf('128', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | (m1_subset_1 @ X0 @ 
% 4.51/4.68             (k1_zfmisc_1 @ 
% 4.51/4.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['126', '127'])).
% 4.51/4.68  thf('129', plain,
% 4.51/4.68      (((m1_subset_1 @ sk_C @ 
% 4.51/4.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 4.51/4.68        | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68        | ~ (v1_relat_1 @ sk_C))),
% 4.51/4.68      inference('sup+', [status(thm)], ['125', '128'])).
% 4.51/4.68  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('132', plain,
% 4.51/4.68      ((m1_subset_1 @ sk_C @ 
% 4.51/4.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 4.51/4.68      inference('demod', [status(thm)], ['129', '130', '131'])).
% 4.51/4.68  thf(cc2_relset_1, axiom,
% 4.51/4.68    (![A:$i,B:$i,C:$i]:
% 4.51/4.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.51/4.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.51/4.68  thf('133', plain,
% 4.51/4.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.51/4.68         ((v4_relat_1 @ X20 @ X21)
% 4.51/4.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.51/4.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.51/4.68  thf('134', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 4.51/4.68      inference('sup-', [status(thm)], ['132', '133'])).
% 4.51/4.68  thf(t209_relat_1, axiom,
% 4.51/4.68    (![A:$i,B:$i]:
% 4.51/4.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.51/4.68       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 4.51/4.68  thf('135', plain,
% 4.51/4.68      (![X7 : $i, X8 : $i]:
% 4.51/4.68         (((X7) = (k7_relat_1 @ X7 @ X8))
% 4.51/4.68          | ~ (v4_relat_1 @ X7 @ X8)
% 4.51/4.68          | ~ (v1_relat_1 @ X7))),
% 4.51/4.68      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.51/4.68  thf('136', plain,
% 4.51/4.68      ((~ (v1_relat_1 @ sk_C)
% 4.51/4.68        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['134', '135'])).
% 4.51/4.68  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('138', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 4.51/4.68      inference('demod', [status(thm)], ['136', '137'])).
% 4.51/4.68  thf(t148_relat_1, axiom,
% 4.51/4.68    (![A:$i,B:$i]:
% 4.51/4.68     ( ( v1_relat_1 @ B ) =>
% 4.51/4.68       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 4.51/4.68  thf('139', plain,
% 4.51/4.68      (![X4 : $i, X5 : $i]:
% 4.51/4.68         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 4.51/4.68          | ~ (v1_relat_1 @ X4))),
% 4.51/4.68      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.51/4.68  thf('140', plain,
% 4.51/4.68      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 4.51/4.68        | ~ (v1_relat_1 @ sk_C))),
% 4.51/4.68      inference('sup+', [status(thm)], ['138', '139'])).
% 4.51/4.68  thf('141', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.51/4.68      inference('sup+', [status(thm)], ['14', '15'])).
% 4.51/4.68  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('143', plain, (((sk_B) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 4.51/4.68      inference('demod', [status(thm)], ['140', '141', '142'])).
% 4.51/4.68  thf(t154_funct_1, axiom,
% 4.51/4.68    (![A:$i,B:$i]:
% 4.51/4.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.51/4.68       ( ( v2_funct_1 @ B ) =>
% 4.51/4.68         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 4.51/4.68  thf('144', plain,
% 4.51/4.68      (![X13 : $i, X14 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X13)
% 4.51/4.68          | ((k9_relat_1 @ X13 @ X14)
% 4.51/4.68              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 4.51/4.68          | ~ (v1_funct_1 @ X13)
% 4.51/4.68          | ~ (v1_relat_1 @ X13))),
% 4.51/4.68      inference('cnf', [status(esa)], [t154_funct_1])).
% 4.51/4.68  thf('145', plain,
% 4.51/4.68      (![X12 : $i]:
% 4.51/4.68         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 4.51/4.68          | ~ (v1_funct_1 @ X12)
% 4.51/4.68          | ~ (v1_relat_1 @ X12))),
% 4.51/4.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.51/4.68  thf('146', plain,
% 4.51/4.68      (![X15 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X15)
% 4.51/4.68          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 4.51/4.68          | ~ (v1_funct_1 @ X15)
% 4.51/4.68          | ~ (v1_relat_1 @ X15))),
% 4.51/4.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.51/4.68  thf(t169_relat_1, axiom,
% 4.51/4.68    (![A:$i]:
% 4.51/4.68     ( ( v1_relat_1 @ A ) =>
% 4.51/4.68       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 4.51/4.68  thf('147', plain,
% 4.51/4.68      (![X6 : $i]:
% 4.51/4.68         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 4.51/4.68          | ~ (v1_relat_1 @ X6))),
% 4.51/4.68      inference('cnf', [status(esa)], [t169_relat_1])).
% 4.51/4.68  thf('148', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 4.51/4.68            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.51/4.68      inference('sup+', [status(thm)], ['146', '147'])).
% 4.51/4.68  thf('149', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 4.51/4.68              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['145', '148'])).
% 4.51/4.68  thf('150', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (((k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 4.51/4.68            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0))),
% 4.51/4.68      inference('simplify', [status(thm)], ['149'])).
% 4.51/4.68  thf('151', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 4.51/4.68            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v2_funct_1 @ X0))),
% 4.51/4.68      inference('sup+', [status(thm)], ['144', '150'])).
% 4.51/4.68  thf('152', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v2_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_funct_1 @ X0)
% 4.51/4.68          | ~ (v1_relat_1 @ X0)
% 4.51/4.68          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 4.51/4.68              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 4.51/4.68      inference('simplify', [status(thm)], ['151'])).
% 4.51/4.68  thf('153', plain,
% 4.51/4.68      ((((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.51/4.68        | ~ (v1_relat_1 @ sk_C)
% 4.51/4.68        | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68        | ~ (v2_funct_1 @ sk_C))),
% 4.51/4.68      inference('sup+', [status(thm)], ['143', '152'])).
% 4.51/4.68  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('157', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.51/4.68      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 4.51/4.68  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('161', plain,
% 4.51/4.68      ((![X0 : $i]:
% 4.51/4.68          (~ (r1_tarski @ sk_A @ X0)
% 4.51/4.68           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 4.51/4.68           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.51/4.68           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 4.51/4.68         <= (~
% 4.51/4.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.51/4.68      inference('demod', [status(thm)], ['124', '157', '158', '159', '160'])).
% 4.51/4.68  thf('162', plain,
% 4.51/4.68      (~
% 4.51/4.68       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.51/4.68      inference('sat_resolution*', [status(thm)], ['10', '99', '100'])).
% 4.51/4.68  thf('163', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (r1_tarski @ sk_A @ X0)
% 4.51/4.68          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 4.51/4.68          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.51/4.68      inference('simpl_trail', [status(thm)], ['161', '162'])).
% 4.51/4.68  thf('164', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ sk_C)
% 4.51/4.68          | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.51/4.68          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 4.51/4.68          | ~ (r1_tarski @ sk_A @ X0))),
% 4.51/4.68      inference('sup-', [status(thm)], ['105', '163'])).
% 4.51/4.68  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('167', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.51/4.68          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 4.51/4.68          | ~ (r1_tarski @ sk_A @ X0))),
% 4.51/4.68      inference('demod', [status(thm)], ['164', '165', '166'])).
% 4.51/4.68  thf('168', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (v1_relat_1 @ sk_C)
% 4.51/4.68          | ~ (v1_funct_1 @ sk_C)
% 4.51/4.68          | ~ (r1_tarski @ sk_A @ X0)
% 4.51/4.68          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 4.51/4.68      inference('sup-', [status(thm)], ['104', '167'])).
% 4.51/4.68  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 4.51/4.68      inference('sup-', [status(thm)], ['2', '3'])).
% 4.51/4.68  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 4.51/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.51/4.68  thf('171', plain,
% 4.51/4.68      (![X0 : $i]:
% 4.51/4.68         (~ (r1_tarski @ sk_A @ X0)
% 4.51/4.68          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 4.51/4.68      inference('demod', [status(thm)], ['168', '169', '170'])).
% 4.51/4.68  thf('172', plain,
% 4.51/4.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.51/4.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.51/4.68      inference('sup-', [status(thm)], ['103', '171'])).
% 4.51/4.68  thf('173', plain, ($false), inference('demod', [status(thm)], ['102', '172'])).
% 4.51/4.68  
% 4.51/4.68  % SZS output end Refutation
% 4.51/4.68  
% 4.51/4.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
