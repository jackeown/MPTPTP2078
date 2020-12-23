%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ln0iFlR70P

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:28 EST 2020

% Result     : Theorem 12.48s
% Output     : Refutation 12.48s
% Verified   : 
% Statistics : Number of formulae       :  241 (1465 expanded)
%              Number of leaves         :   47 ( 478 expanded)
%              Depth                    :   30
%              Number of atoms          : 1575 (20468 expanded)
%              Number of equality atoms :  105 ( 788 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('29',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('30',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','31'])).

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

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('37',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('58',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('59',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('71',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('72',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('73',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('79',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','83'])).

thf('85',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('86',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('88',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('90',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('91',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('94',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('95',plain,(
    ! [X14: $i] :
      ( ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('99',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93','99'])).

thf('101',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93','99'])).

thf('102',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('103',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('105',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('106',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('107',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('108',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('109',plain,(
    ! [X12: $i] :
      ( ( ( k2_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('110',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93','99'])).

thf('112',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('115',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('116',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('122',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('123',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('125',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','131'])).

thf('133',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('137',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('139',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('143',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['66','67'])).

thf('146',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('148',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('149',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('150',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('155',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143','146','147','153','154','155','156','157','158'])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','159'])).

thf('161',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['20','160'])).

thf('162',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','161','162'])).

thf('164',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','163'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('167',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('171',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('174',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['169','174'])).

thf('176',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['168','175'])).

thf('177',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('178',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('180',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','161','162'])).

thf('182',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['180','181'])).

thf('183',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','182'])).

thf('184',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('185',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['183','186'])).

thf('188',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('189',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('190',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('191',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,(
    $false ),
    inference(demod,[status(thm)],['164','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ln0iFlR70P
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 12.48/12.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.48/12.67  % Solved by: fo/fo7.sh
% 12.48/12.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.48/12.67  % done 11591 iterations in 12.211s
% 12.48/12.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.48/12.67  % SZS output start Refutation
% 12.48/12.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.48/12.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.48/12.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.48/12.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.48/12.67  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 12.48/12.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.48/12.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.48/12.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.48/12.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.48/12.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 12.48/12.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 12.48/12.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.48/12.67  thf(sk_A_type, type, sk_A: $i).
% 12.48/12.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 12.48/12.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.48/12.67  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 12.48/12.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 12.48/12.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.48/12.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.48/12.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 12.48/12.67  thf(sk_C_type, type, sk_C: $i).
% 12.48/12.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.48/12.67  thf(sk_B_type, type, sk_B: $i).
% 12.48/12.67  thf(t31_funct_2, conjecture,
% 12.48/12.67    (![A:$i,B:$i,C:$i]:
% 12.48/12.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.48/12.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.48/12.67       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 12.48/12.67         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 12.48/12.67           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 12.48/12.67           ( m1_subset_1 @
% 12.48/12.67             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 12.48/12.67  thf(zf_stmt_0, negated_conjecture,
% 12.48/12.67    (~( ![A:$i,B:$i,C:$i]:
% 12.48/12.67        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.48/12.67            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.48/12.67          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 12.48/12.67            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 12.48/12.67              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 12.48/12.67              ( m1_subset_1 @
% 12.48/12.67                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 12.48/12.67    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 12.48/12.67  thf('0', plain,
% 12.48/12.67      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.48/12.67        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 12.48/12.67        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('1', plain,
% 12.48/12.67      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('split', [status(esa)], ['0'])).
% 12.48/12.67  thf('2', plain,
% 12.48/12.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf(cc1_relset_1, axiom,
% 12.48/12.67    (![A:$i,B:$i,C:$i]:
% 12.48/12.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.48/12.67       ( v1_relat_1 @ C ) ))).
% 12.48/12.67  thf('3', plain,
% 12.48/12.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 12.48/12.67         ((v1_relat_1 @ X19)
% 12.48/12.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 12.48/12.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.48/12.67  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf(d9_funct_1, axiom,
% 12.48/12.67    (![A:$i]:
% 12.48/12.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.48/12.67       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 12.48/12.67  thf('5', plain,
% 12.48/12.67      (![X15 : $i]:
% 12.48/12.67         (~ (v2_funct_1 @ X15)
% 12.48/12.67          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 12.48/12.67          | ~ (v1_funct_1 @ X15)
% 12.48/12.67          | ~ (v1_relat_1 @ X15))),
% 12.48/12.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 12.48/12.67  thf('6', plain,
% 12.48/12.67      ((~ (v1_funct_1 @ sk_C)
% 12.48/12.67        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 12.48/12.67        | ~ (v2_funct_1 @ sk_C))),
% 12.48/12.67      inference('sup-', [status(thm)], ['4', '5'])).
% 12.48/12.67  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('10', plain,
% 12.48/12.67      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 12.48/12.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('demod', [status(thm)], ['1', '9'])).
% 12.48/12.67  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf(dt_k2_funct_1, axiom,
% 12.48/12.67    (![A:$i]:
% 12.48/12.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.48/12.67       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 12.48/12.67         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 12.48/12.67  thf('12', plain,
% 12.48/12.67      (![X16 : $i]:
% 12.48/12.67         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 12.48/12.67          | ~ (v1_funct_1 @ X16)
% 12.48/12.67          | ~ (v1_relat_1 @ X16))),
% 12.48/12.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.48/12.67  thf('13', plain,
% 12.48/12.67      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 12.48/12.67         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.48/12.67      inference('split', [status(esa)], ['0'])).
% 12.48/12.67  thf('14', plain,
% 12.48/12.67      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 12.48/12.67         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.48/12.67      inference('sup-', [status(thm)], ['12', '13'])).
% 12.48/12.67  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('16', plain,
% 12.48/12.67      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 12.48/12.67      inference('demod', [status(thm)], ['14', '15'])).
% 12.48/12.67  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['11', '16'])).
% 12.48/12.67  thf('18', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('19', plain,
% 12.48/12.67      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('split', [status(esa)], ['0'])).
% 12.48/12.67  thf('20', plain,
% 12.48/12.67      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['18', '19'])).
% 12.48/12.67  thf(d10_xboole_0, axiom,
% 12.48/12.67    (![A:$i,B:$i]:
% 12.48/12.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.48/12.67  thf('21', plain,
% 12.48/12.67      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 12.48/12.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.48/12.67  thf('22', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 12.48/12.67      inference('simplify', [status(thm)], ['21'])).
% 12.48/12.67  thf(l13_xboole_0, axiom,
% 12.48/12.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 12.48/12.67  thf('23', plain,
% 12.48/12.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.48/12.67  thf(t60_relat_1, axiom,
% 12.48/12.67    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 12.48/12.67     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 12.48/12.67  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.48/12.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 12.48/12.67  thf(t4_funct_2, axiom,
% 12.48/12.67    (![A:$i,B:$i]:
% 12.48/12.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 12.48/12.67       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 12.48/12.67         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 12.48/12.67           ( m1_subset_1 @
% 12.48/12.67             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 12.48/12.67  thf('25', plain,
% 12.48/12.67      (![X36 : $i, X37 : $i]:
% 12.48/12.67         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 12.48/12.67          | (v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ X37)
% 12.48/12.67          | ~ (v1_funct_1 @ X36)
% 12.48/12.67          | ~ (v1_relat_1 @ X36))),
% 12.48/12.67      inference('cnf', [status(esa)], [t4_funct_2])).
% 12.48/12.67  thf('26', plain,
% 12.48/12.67      (![X0 : $i]:
% 12.48/12.67         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 12.48/12.67          | ~ (v1_relat_1 @ k1_xboole_0)
% 12.48/12.67          | ~ (v1_funct_1 @ k1_xboole_0)
% 12.48/12.67          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 12.48/12.67      inference('sup-', [status(thm)], ['24', '25'])).
% 12.48/12.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 12.48/12.67  thf('27', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 12.48/12.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.48/12.67  thf(t45_ordinal1, axiom,
% 12.48/12.67    (![A:$i]:
% 12.48/12.67     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 12.48/12.67       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 12.48/12.67  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('29', plain, ((v1_funct_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('30', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.48/12.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 12.48/12.67  thf('31', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 12.48/12.67      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 12.48/12.67  thf('32', plain,
% 12.48/12.67      (![X0 : $i, X1 : $i]:
% 12.48/12.67         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('sup+', [status(thm)], ['23', '31'])).
% 12.48/12.67  thf(d1_funct_2, axiom,
% 12.48/12.67    (![A:$i,B:$i,C:$i]:
% 12.48/12.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.48/12.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.48/12.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 12.48/12.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 12.48/12.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.48/12.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 12.48/12.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 12.48/12.67  thf(zf_stmt_1, axiom,
% 12.48/12.67    (![B:$i,A:$i]:
% 12.48/12.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.48/12.67       ( zip_tseitin_0 @ B @ A ) ))).
% 12.48/12.67  thf('33', plain,
% 12.48/12.67      (![X28 : $i, X29 : $i]:
% 12.48/12.67         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.48/12.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 12.48/12.67  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.48/12.67  thf('35', plain,
% 12.48/12.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 12.48/12.67      inference('sup+', [status(thm)], ['33', '34'])).
% 12.48/12.67  thf('36', plain,
% 12.48/12.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.48/12.67  thf(zf_stmt_3, axiom,
% 12.48/12.67    (![C:$i,B:$i,A:$i]:
% 12.48/12.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 12.48/12.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 12.48/12.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 12.48/12.67  thf(zf_stmt_5, axiom,
% 12.48/12.67    (![A:$i,B:$i,C:$i]:
% 12.48/12.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.48/12.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 12.48/12.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.48/12.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 12.48/12.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 12.48/12.67  thf('37', plain,
% 12.48/12.67      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.48/12.67         (~ (zip_tseitin_0 @ X33 @ X34)
% 12.48/12.67          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 12.48/12.67          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.48/12.67  thf('38', plain,
% 12.48/12.67      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 12.48/12.67      inference('sup-', [status(thm)], ['36', '37'])).
% 12.48/12.67  thf('39', plain,
% 12.48/12.67      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 12.48/12.67      inference('sup-', [status(thm)], ['35', '38'])).
% 12.48/12.67  thf('40', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('41', plain,
% 12.48/12.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 12.48/12.67         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 12.48/12.67          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 12.48/12.67          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.48/12.67  thf('42', plain,
% 12.48/12.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 12.48/12.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['40', '41'])).
% 12.48/12.67  thf('43', plain,
% 12.48/12.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf(redefinition_k1_relset_1, axiom,
% 12.48/12.67    (![A:$i,B:$i,C:$i]:
% 12.48/12.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.48/12.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 12.48/12.67  thf('44', plain,
% 12.48/12.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 12.48/12.67         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 12.48/12.67          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 12.48/12.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.48/12.67  thf('45', plain,
% 12.48/12.67      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 12.48/12.67      inference('sup-', [status(thm)], ['43', '44'])).
% 12.48/12.67  thf('46', plain,
% 12.48/12.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['42', '45'])).
% 12.48/12.67  thf('47', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['39', '46'])).
% 12.48/12.67  thf('48', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf(t55_funct_1, axiom,
% 12.48/12.67    (![A:$i]:
% 12.48/12.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.48/12.67       ( ( v2_funct_1 @ A ) =>
% 12.48/12.67         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 12.48/12.67           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 12.48/12.67  thf('49', plain,
% 12.48/12.67      (![X17 : $i]:
% 12.48/12.67         (~ (v2_funct_1 @ X17)
% 12.48/12.67          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 12.48/12.67          | ~ (v1_funct_1 @ X17)
% 12.48/12.67          | ~ (v1_relat_1 @ X17))),
% 12.48/12.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.48/12.67  thf('50', plain,
% 12.48/12.67      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 12.48/12.67        | ~ (v1_relat_1 @ sk_C)
% 12.48/12.67        | ~ (v1_funct_1 @ sk_C)
% 12.48/12.67        | ~ (v2_funct_1 @ sk_C))),
% 12.48/12.67      inference('sup+', [status(thm)], ['48', '49'])).
% 12.48/12.67  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('54', plain,
% 12.48/12.67      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 12.48/12.67  thf(fc8_relat_1, axiom,
% 12.48/12.67    (![A:$i]:
% 12.48/12.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 12.48/12.67       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 12.48/12.67  thf('55', plain,
% 12.48/12.67      (![X11 : $i]:
% 12.48/12.67         (~ (v1_xboole_0 @ (k1_relat_1 @ X11))
% 12.48/12.67          | ~ (v1_relat_1 @ X11)
% 12.48/12.67          | (v1_xboole_0 @ X11))),
% 12.48/12.67      inference('cnf', [status(esa)], [fc8_relat_1])).
% 12.48/12.67  thf('56', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 12.48/12.67        | (v1_xboole_0 @ (k4_relat_1 @ sk_C))
% 12.48/12.67        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['54', '55'])).
% 12.48/12.67  thf('57', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('58', plain,
% 12.48/12.67      (![X16 : $i]:
% 12.48/12.67         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 12.48/12.67          | ~ (v1_funct_1 @ X16)
% 12.48/12.67          | ~ (v1_relat_1 @ X16))),
% 12.48/12.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.48/12.67  thf('59', plain,
% 12.48/12.67      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 12.48/12.67        | ~ (v1_relat_1 @ sk_C)
% 12.48/12.67        | ~ (v1_funct_1 @ sk_C))),
% 12.48/12.67      inference('sup+', [status(thm)], ['57', '58'])).
% 12.48/12.67  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('62', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['59', '60', '61'])).
% 12.48/12.67  thf('63', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 12.48/12.67        | (v1_xboole_0 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['56', '62'])).
% 12.48/12.67  thf('64', plain,
% 12.48/12.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf(redefinition_k2_relset_1, axiom,
% 12.48/12.67    (![A:$i,B:$i,C:$i]:
% 12.48/12.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.48/12.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 12.48/12.67  thf('65', plain,
% 12.48/12.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 12.48/12.67         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 12.48/12.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 12.48/12.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 12.48/12.67  thf('66', plain,
% 12.48/12.67      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 12.48/12.67      inference('sup-', [status(thm)], ['64', '65'])).
% 12.48/12.67  thf('67', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('68', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.48/12.67      inference('sup+', [status(thm)], ['66', '67'])).
% 12.48/12.67  thf('69', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['63', '68'])).
% 12.48/12.67  thf('70', plain,
% 12.48/12.67      ((((sk_A) = (k1_relat_1 @ sk_C)) | (v1_xboole_0 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['47', '69'])).
% 12.48/12.67  thf('71', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('72', plain,
% 12.48/12.67      (![X17 : $i]:
% 12.48/12.67         (~ (v2_funct_1 @ X17)
% 12.48/12.67          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 12.48/12.67          | ~ (v1_funct_1 @ X17)
% 12.48/12.67          | ~ (v1_relat_1 @ X17))),
% 12.48/12.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.48/12.67  thf('73', plain,
% 12.48/12.67      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 12.48/12.67        | ~ (v1_relat_1 @ sk_C)
% 12.48/12.67        | ~ (v1_funct_1 @ sk_C)
% 12.48/12.67        | ~ (v2_funct_1 @ sk_C))),
% 12.48/12.67      inference('sup+', [status(thm)], ['71', '72'])).
% 12.48/12.67  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('76', plain, ((v2_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('77', plain,
% 12.48/12.67      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 12.48/12.67  thf('78', plain,
% 12.48/12.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.48/12.67  thf('79', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.48/12.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 12.48/12.67  thf('80', plain,
% 12.48/12.67      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('sup+', [status(thm)], ['78', '79'])).
% 12.48/12.67  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.48/12.67  thf('82', plain,
% 12.48/12.67      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('sup+', [status(thm)], ['80', '81'])).
% 12.48/12.67  thf('83', plain,
% 12.48/12.67      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 12.48/12.67        | ~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup+', [status(thm)], ['77', '82'])).
% 12.48/12.67  thf('84', plain,
% 12.48/12.67      ((((sk_A) = (k1_relat_1 @ sk_C)) | (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['70', '83'])).
% 12.48/12.67  thf('85', plain,
% 12.48/12.67      (![X11 : $i]:
% 12.48/12.67         (~ (v1_xboole_0 @ (k1_relat_1 @ X11))
% 12.48/12.67          | ~ (v1_relat_1 @ X11)
% 12.48/12.67          | (v1_xboole_0 @ X11))),
% 12.48/12.67      inference('cnf', [status(esa)], [fc8_relat_1])).
% 12.48/12.67  thf('86', plain,
% 12.48/12.67      ((((sk_A) = (k1_relat_1 @ sk_C))
% 12.48/12.67        | (v1_xboole_0 @ sk_C)
% 12.48/12.67        | ~ (v1_relat_1 @ sk_C))),
% 12.48/12.67      inference('sup-', [status(thm)], ['84', '85'])).
% 12.48/12.67  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf('88', plain, ((((sk_A) = (k1_relat_1 @ sk_C)) | (v1_xboole_0 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['86', '87'])).
% 12.48/12.67  thf('89', plain,
% 12.48/12.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.48/12.67  thf('90', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('91', plain,
% 12.48/12.67      (![X15 : $i]:
% 12.48/12.67         (~ (v2_funct_1 @ X15)
% 12.48/12.67          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 12.48/12.67          | ~ (v1_funct_1 @ X15)
% 12.48/12.67          | ~ (v1_relat_1 @ X15))),
% 12.48/12.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 12.48/12.67  thf('92', plain,
% 12.48/12.67      ((~ (v1_funct_1 @ k1_xboole_0)
% 12.48/12.67        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 12.48/12.67        | ~ (v2_funct_1 @ k1_xboole_0))),
% 12.48/12.67      inference('sup-', [status(thm)], ['90', '91'])).
% 12.48/12.67  thf('93', plain, ((v1_funct_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('94', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf(cc2_funct_1, axiom,
% 12.48/12.67    (![A:$i]:
% 12.48/12.67     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.48/12.67       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 12.48/12.67  thf('95', plain,
% 12.48/12.67      (![X14 : $i]:
% 12.48/12.67         ((v2_funct_1 @ X14)
% 12.48/12.67          | ~ (v1_funct_1 @ X14)
% 12.48/12.67          | ~ (v1_relat_1 @ X14)
% 12.48/12.67          | ~ (v1_xboole_0 @ X14))),
% 12.48/12.67      inference('cnf', [status(esa)], [cc2_funct_1])).
% 12.48/12.67  thf('96', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 12.48/12.67        | ~ (v1_funct_1 @ k1_xboole_0)
% 12.48/12.67        | (v2_funct_1 @ k1_xboole_0))),
% 12.48/12.67      inference('sup-', [status(thm)], ['94', '95'])).
% 12.48/12.67  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.48/12.67  thf('98', plain, ((v1_funct_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('99', plain, ((v2_funct_1 @ k1_xboole_0)),
% 12.48/12.67      inference('demod', [status(thm)], ['96', '97', '98'])).
% 12.48/12.67  thf('100', plain,
% 12.48/12.67      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 12.48/12.67      inference('demod', [status(thm)], ['92', '93', '99'])).
% 12.48/12.67  thf('101', plain,
% 12.48/12.67      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 12.48/12.67      inference('demod', [status(thm)], ['92', '93', '99'])).
% 12.48/12.67  thf('102', plain,
% 12.48/12.67      (![X17 : $i]:
% 12.48/12.67         (~ (v2_funct_1 @ X17)
% 12.48/12.67          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 12.48/12.67          | ~ (v1_funct_1 @ X17)
% 12.48/12.67          | ~ (v1_relat_1 @ X17))),
% 12.48/12.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.48/12.67  thf('103', plain,
% 12.48/12.67      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))
% 12.48/12.67        | ~ (v1_relat_1 @ k1_xboole_0)
% 12.48/12.67        | ~ (v1_funct_1 @ k1_xboole_0)
% 12.48/12.67        | ~ (v2_funct_1 @ k1_xboole_0))),
% 12.48/12.67      inference('sup+', [status(thm)], ['101', '102'])).
% 12.48/12.67  thf('104', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.48/12.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 12.48/12.67  thf('105', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('106', plain, ((v1_funct_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('107', plain, ((v2_funct_1 @ k1_xboole_0)),
% 12.48/12.67      inference('demod', [status(thm)], ['96', '97', '98'])).
% 12.48/12.67  thf('108', plain,
% 12.48/12.67      (((k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 12.48/12.67      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 12.48/12.67  thf(t65_relat_1, axiom,
% 12.48/12.67    (![A:$i]:
% 12.48/12.67     ( ( v1_relat_1 @ A ) =>
% 12.48/12.67       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 12.48/12.67         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 12.48/12.67  thf('109', plain,
% 12.48/12.67      (![X12 : $i]:
% 12.48/12.67         (((k2_relat_1 @ X12) != (k1_xboole_0))
% 12.48/12.67          | ((k1_relat_1 @ X12) = (k1_xboole_0))
% 12.48/12.67          | ~ (v1_relat_1 @ X12))),
% 12.48/12.67      inference('cnf', [status(esa)], [t65_relat_1])).
% 12.48/12.67  thf('110', plain,
% 12.48/12.67      ((((k1_xboole_0) != (k1_xboole_0))
% 12.48/12.67        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 12.48/12.67        | ((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['108', '109'])).
% 12.48/12.67  thf('111', plain,
% 12.48/12.67      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 12.48/12.67      inference('demod', [status(thm)], ['92', '93', '99'])).
% 12.48/12.67  thf('112', plain,
% 12.48/12.67      (![X16 : $i]:
% 12.48/12.67         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 12.48/12.67          | ~ (v1_funct_1 @ X16)
% 12.48/12.67          | ~ (v1_relat_1 @ X16))),
% 12.48/12.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.48/12.67  thf('113', plain,
% 12.48/12.67      (((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 12.48/12.67        | ~ (v1_relat_1 @ k1_xboole_0)
% 12.48/12.67        | ~ (v1_funct_1 @ k1_xboole_0))),
% 12.48/12.67      inference('sup+', [status(thm)], ['111', '112'])).
% 12.48/12.67  thf('114', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('115', plain, ((v1_funct_1 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [t45_ordinal1])).
% 12.48/12.67  thf('116', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 12.48/12.67      inference('demod', [status(thm)], ['113', '114', '115'])).
% 12.48/12.67  thf('117', plain,
% 12.48/12.67      ((((k1_xboole_0) != (k1_xboole_0))
% 12.48/12.67        | ((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 12.48/12.67      inference('demod', [status(thm)], ['110', '116'])).
% 12.48/12.67  thf('118', plain,
% 12.48/12.67      (((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 12.48/12.67      inference('simplify', [status(thm)], ['117'])).
% 12.48/12.67  thf('119', plain,
% 12.48/12.67      (![X11 : $i]:
% 12.48/12.67         (~ (v1_xboole_0 @ (k1_relat_1 @ X11))
% 12.48/12.67          | ~ (v1_relat_1 @ X11)
% 12.48/12.67          | (v1_xboole_0 @ X11))),
% 12.48/12.67      inference('cnf', [status(esa)], [fc8_relat_1])).
% 12.48/12.67  thf('120', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 12.48/12.67        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))
% 12.48/12.67        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['118', '119'])).
% 12.48/12.67  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.48/12.67  thf('122', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 12.48/12.67      inference('demod', [status(thm)], ['113', '114', '115'])).
% 12.48/12.67  thf('123', plain, ((v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 12.48/12.67      inference('demod', [status(thm)], ['120', '121', '122'])).
% 12.48/12.67  thf('124', plain,
% 12.48/12.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.48/12.67  thf('125', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.48/12.67      inference('sup-', [status(thm)], ['123', '124'])).
% 12.48/12.67  thf('126', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.48/12.67      inference('demod', [status(thm)], ['100', '125'])).
% 12.48/12.67  thf('127', plain,
% 12.48/12.67      (![X0 : $i]: (((k2_funct_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('sup+', [status(thm)], ['89', '126'])).
% 12.48/12.67  thf('128', plain,
% 12.48/12.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.48/12.67  thf('129', plain,
% 12.48/12.67      (![X0 : $i, X1 : $i]:
% 12.48/12.67         (((X1) = (k2_funct_1 @ X0))
% 12.48/12.67          | ~ (v1_xboole_0 @ X0)
% 12.48/12.67          | ~ (v1_xboole_0 @ X1))),
% 12.48/12.67      inference('sup+', [status(thm)], ['127', '128'])).
% 12.48/12.67  thf('130', plain,
% 12.48/12.67      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('split', [status(esa)], ['0'])).
% 12.48/12.67  thf('131', plain,
% 12.48/12.67      ((![X0 : $i]:
% 12.48/12.67          (~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 12.48/12.67           | ~ (v1_xboole_0 @ X0)
% 12.48/12.67           | ~ (v1_xboole_0 @ sk_C)))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['129', '130'])).
% 12.48/12.67  thf('132', plain,
% 12.48/12.67      ((![X0 : $i]:
% 12.48/12.67          (((sk_A) = (k1_relat_1 @ sk_C))
% 12.48/12.67           | ~ (v1_xboole_0 @ X0)
% 12.48/12.67           | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['88', '131'])).
% 12.48/12.67  thf('133', plain,
% 12.48/12.67      (((~ (v1_xboole_0 @ sk_B)
% 12.48/12.67         | ~ (v1_xboole_0 @ k1_xboole_0)
% 12.48/12.67         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['32', '132'])).
% 12.48/12.67  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.48/12.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.48/12.67  thf('135', plain,
% 12.48/12.67      (((~ (v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('demod', [status(thm)], ['133', '134'])).
% 12.48/12.67  thf('136', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['39', '46'])).
% 12.48/12.67  thf('137', plain,
% 12.48/12.67      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('clc', [status(thm)], ['135', '136'])).
% 12.48/12.67  thf('138', plain,
% 12.48/12.67      (![X17 : $i]:
% 12.48/12.67         (~ (v2_funct_1 @ X17)
% 12.48/12.67          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 12.48/12.67          | ~ (v1_funct_1 @ X17)
% 12.48/12.67          | ~ (v1_relat_1 @ X17))),
% 12.48/12.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.48/12.67  thf('139', plain,
% 12.48/12.67      (![X36 : $i, X37 : $i]:
% 12.48/12.67         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 12.48/12.67          | (v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ X37)
% 12.48/12.67          | ~ (v1_funct_1 @ X36)
% 12.48/12.67          | ~ (v1_relat_1 @ X36))),
% 12.48/12.67      inference('cnf', [status(esa)], [t4_funct_2])).
% 12.48/12.67  thf('140', plain,
% 12.48/12.67      (![X0 : $i, X1 : $i]:
% 12.48/12.67         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 12.48/12.67          | ~ (v1_relat_1 @ X0)
% 12.48/12.67          | ~ (v1_funct_1 @ X0)
% 12.48/12.67          | ~ (v2_funct_1 @ X0)
% 12.48/12.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 12.48/12.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 12.48/12.67          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 12.48/12.67             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 12.48/12.67      inference('sup-', [status(thm)], ['138', '139'])).
% 12.48/12.67  thf('141', plain,
% 12.48/12.67      ((![X0 : $i]:
% 12.48/12.67          (~ (r1_tarski @ sk_A @ X0)
% 12.48/12.67           | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67              (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 12.48/12.67           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 12.48/12.67           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 12.48/12.67           | ~ (v2_funct_1 @ sk_C)
% 12.48/12.67           | ~ (v1_funct_1 @ sk_C)
% 12.48/12.67           | ~ (v1_relat_1 @ sk_C)))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['137', '140'])).
% 12.48/12.67  thf('142', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('143', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('144', plain,
% 12.48/12.67      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 12.48/12.67  thf('145', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 12.48/12.67      inference('sup+', [status(thm)], ['66', '67'])).
% 12.48/12.67  thf('146', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['144', '145'])).
% 12.48/12.67  thf('147', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('148', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('149', plain,
% 12.48/12.67      (![X16 : $i]:
% 12.48/12.67         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 12.48/12.67          | ~ (v1_funct_1 @ X16)
% 12.48/12.67          | ~ (v1_relat_1 @ X16))),
% 12.48/12.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 12.48/12.67  thf('150', plain,
% 12.48/12.67      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 12.48/12.67        | ~ (v1_relat_1 @ sk_C)
% 12.48/12.67        | ~ (v1_funct_1 @ sk_C))),
% 12.48/12.67      inference('sup+', [status(thm)], ['148', '149'])).
% 12.48/12.67  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('153', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['150', '151', '152'])).
% 12.48/12.67  thf('154', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('155', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['59', '60', '61'])).
% 12.48/12.67  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 12.48/12.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.48/12.67  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 12.48/12.67      inference('sup-', [status(thm)], ['2', '3'])).
% 12.48/12.67  thf('159', plain,
% 12.48/12.67      ((![X0 : $i]:
% 12.48/12.67          (~ (r1_tarski @ sk_A @ X0)
% 12.48/12.67           | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ X0)))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('demod', [status(thm)],
% 12.48/12.67                ['141', '142', '143', '146', '147', '153', '154', '155', 
% 12.48/12.67                 '156', '157', '158'])).
% 12.48/12.67  thf('160', plain,
% 12.48/12.67      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 12.48/12.67         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['22', '159'])).
% 12.48/12.67  thf('161', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 12.48/12.67      inference('demod', [status(thm)], ['20', '160'])).
% 12.48/12.67  thf('162', plain,
% 12.48/12.67      (~
% 12.48/12.67       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 12.48/12.67       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 12.48/12.67       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 12.48/12.67      inference('split', [status(esa)], ['0'])).
% 12.48/12.67  thf('163', plain,
% 12.48/12.67      (~
% 12.48/12.67       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.48/12.67      inference('sat_resolution*', [status(thm)], ['17', '161', '162'])).
% 12.48/12.67  thf('164', plain,
% 12.48/12.67      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 12.48/12.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.48/12.67      inference('simpl_trail', [status(thm)], ['10', '163'])).
% 12.48/12.67  thf('165', plain,
% 12.48/12.67      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 12.48/12.67  thf('166', plain,
% 12.48/12.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 12.48/12.67      inference('sup+', [status(thm)], ['33', '34'])).
% 12.48/12.67  thf('167', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['63', '68'])).
% 12.48/12.67  thf('168', plain,
% 12.48/12.67      (![X0 : $i]:
% 12.48/12.67         ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup-', [status(thm)], ['166', '167'])).
% 12.48/12.67  thf('169', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['6', '7', '8'])).
% 12.48/12.67  thf('170', plain,
% 12.48/12.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.48/12.67  thf(t4_subset_1, axiom,
% 12.48/12.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 12.48/12.67  thf('171', plain,
% 12.48/12.67      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 12.48/12.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.48/12.67  thf('172', plain,
% 12.48/12.67      (![X0 : $i, X1 : $i]:
% 12.48/12.67         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 12.48/12.67      inference('sup+', [status(thm)], ['170', '171'])).
% 12.48/12.67  thf('173', plain,
% 12.48/12.67      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('split', [status(esa)], ['0'])).
% 12.48/12.67  thf('174', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('sup-', [status(thm)], ['172', '173'])).
% 12.48/12.67  thf('175', plain,
% 12.48/12.67      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('sup-', [status(thm)], ['169', '174'])).
% 12.48/12.67  thf('176', plain,
% 12.48/12.67      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('sup-', [status(thm)], ['168', '175'])).
% 12.48/12.67  thf('177', plain,
% 12.48/12.67      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 12.48/12.67      inference('sup-', [status(thm)], ['36', '37'])).
% 12.48/12.67  thf('178', plain,
% 12.48/12.67      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('sup-', [status(thm)], ['176', '177'])).
% 12.48/12.67  thf('179', plain,
% 12.48/12.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['42', '45'])).
% 12.48/12.67  thf('180', plain,
% 12.48/12.67      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 12.48/12.67         <= (~
% 12.48/12.67             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 12.48/12.67      inference('sup-', [status(thm)], ['178', '179'])).
% 12.48/12.67  thf('181', plain,
% 12.48/12.67      (~
% 12.48/12.67       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 12.48/12.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 12.48/12.67      inference('sat_resolution*', [status(thm)], ['17', '161', '162'])).
% 12.48/12.67  thf('182', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 12.48/12.67      inference('simpl_trail', [status(thm)], ['180', '181'])).
% 12.48/12.67  thf('183', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['165', '182'])).
% 12.48/12.67  thf('184', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 12.48/12.67      inference('simplify', [status(thm)], ['21'])).
% 12.48/12.67  thf('185', plain,
% 12.48/12.67      (![X36 : $i, X37 : $i]:
% 12.48/12.67         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 12.48/12.67          | (m1_subset_1 @ X36 @ 
% 12.48/12.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 12.48/12.67          | ~ (v1_funct_1 @ X36)
% 12.48/12.67          | ~ (v1_relat_1 @ X36))),
% 12.48/12.67      inference('cnf', [status(esa)], [t4_funct_2])).
% 12.48/12.67  thf('186', plain,
% 12.48/12.67      (![X0 : $i]:
% 12.48/12.67         (~ (v1_relat_1 @ X0)
% 12.48/12.67          | ~ (v1_funct_1 @ X0)
% 12.48/12.67          | (m1_subset_1 @ X0 @ 
% 12.48/12.67             (k1_zfmisc_1 @ 
% 12.48/12.67              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 12.48/12.67      inference('sup-', [status(thm)], ['184', '185'])).
% 12.48/12.67  thf('187', plain,
% 12.48/12.67      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 12.48/12.67         (k1_zfmisc_1 @ 
% 12.48/12.67          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 12.48/12.67        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 12.48/12.67        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('sup+', [status(thm)], ['183', '186'])).
% 12.48/12.67  thf('188', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 12.48/12.67      inference('demod', [status(thm)], ['144', '145'])).
% 12.48/12.67  thf('189', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['150', '151', '152'])).
% 12.48/12.67  thf('190', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 12.48/12.67      inference('demod', [status(thm)], ['59', '60', '61'])).
% 12.48/12.67  thf('191', plain,
% 12.48/12.67      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 12.48/12.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 12.48/12.67      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 12.48/12.67  thf('192', plain, ($false), inference('demod', [status(thm)], ['164', '191'])).
% 12.48/12.67  
% 12.48/12.67  % SZS output end Refutation
% 12.48/12.67  
% 12.48/12.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
