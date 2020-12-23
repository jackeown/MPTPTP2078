%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.svclDNjuOO

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:32 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 778 expanded)
%              Number of leaves         :   40 ( 241 expanded)
%              Depth                    :   18
%              Number of atoms          : 1033 (12544 expanded)
%              Number of equality atoms :   65 ( 446 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ X2 )
        = ( k4_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_relset_1 @ X19 @ X20 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('23',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','28','29'])).

thf('31',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','30'])).

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

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

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

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['38','51'])).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B_1 )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','30'])).

thf('57',plain,(
    ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','58'])).

thf('60',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','59'])).

thf('61',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X35: $i] :
      ( ( v1_funct_2 @ X35 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('63',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('65',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X1: $i] :
      ( v1_xboole_0 @ ( sk_B @ X1 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('73',plain,(
    ! [X1: $i] :
      ( v1_xboole_0 @ ( sk_B @ X1 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('87',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','58'])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('94',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','94'])).

thf('96',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','57'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['91','97'])).

thf('99',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','98'])).

thf('100',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('101',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('107',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','99','105','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['60','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.svclDNjuOO
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.61/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.77  % Solved by: fo/fo7.sh
% 0.61/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.77  % done 323 iterations in 0.327s
% 0.61/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.77  % SZS output start Refutation
% 0.61/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.77  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.61/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.77  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.61/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.61/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.77  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.77  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.61/0.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.61/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.61/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.77  thf(t31_funct_2, conjecture,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.77       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.61/0.77         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.61/0.77           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.61/0.77           ( m1_subset_1 @
% 0.61/0.77             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.61/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.77        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.77            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.77          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.61/0.77            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.61/0.77              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.61/0.77              ( m1_subset_1 @
% 0.61/0.77                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.61/0.77    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.61/0.77  thf('0', plain,
% 0.61/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.61/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)
% 0.61/0.77        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.61/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('1', plain,
% 0.61/0.77      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 0.61/0.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 0.61/0.77      inference('split', [status(esa)], ['0'])).
% 0.61/0.77  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf(d9_funct_1, axiom,
% 0.61/0.77    (![A:$i]:
% 0.61/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.77       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.61/0.77  thf('3', plain,
% 0.61/0.77      (![X2 : $i]:
% 0.61/0.77         (~ (v2_funct_1 @ X2)
% 0.61/0.77          | ((k2_funct_1 @ X2) = (k4_relat_1 @ X2))
% 0.61/0.77          | ~ (v1_funct_1 @ X2)
% 0.61/0.77          | ~ (v1_relat_1 @ X2))),
% 0.61/0.77      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.61/0.77  thf('4', plain,
% 0.61/0.77      ((~ (v1_relat_1 @ sk_C)
% 0.61/0.77        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.61/0.77        | ~ (v2_funct_1 @ sk_C))),
% 0.61/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.77  thf('5', plain,
% 0.61/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf(cc1_relset_1, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.77       ( v1_relat_1 @ C ) ))).
% 0.61/0.77  thf('6', plain,
% 0.61/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.77         ((v1_relat_1 @ X6)
% 0.61/0.77          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.61/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.77  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.77  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.61/0.77  thf('10', plain,
% 0.61/0.77      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A))
% 0.61/0.77         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 0.61/0.77      inference('demod', [status(thm)], ['1', '9'])).
% 0.61/0.77  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.77  thf(dt_k2_funct_1, axiom,
% 0.61/0.77    (![A:$i]:
% 0.61/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.77       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.61/0.77         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.61/0.77  thf('12', plain,
% 0.61/0.77      (![X3 : $i]:
% 0.61/0.77         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.61/0.77          | ~ (v1_funct_1 @ X3)
% 0.61/0.77          | ~ (v1_relat_1 @ X3))),
% 0.61/0.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.61/0.77  thf('13', plain,
% 0.61/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.61/0.77         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.61/0.77      inference('split', [status(esa)], ['0'])).
% 0.61/0.77  thf('14', plain,
% 0.61/0.77      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.61/0.77         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.61/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.77  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('16', plain,
% 0.61/0.77      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.61/0.77      inference('demod', [status(thm)], ['14', '15'])).
% 0.61/0.77  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['11', '16'])).
% 0.61/0.77  thf('18', plain,
% 0.61/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf(dt_k3_relset_1, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.77       ( m1_subset_1 @
% 0.61/0.77         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.61/0.77         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.61/0.77  thf('19', plain,
% 0.61/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.77         ((m1_subset_1 @ (k3_relset_1 @ X9 @ X10 @ X11) @ 
% 0.61/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.61/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.61/0.77      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.61/0.77  thf('20', plain,
% 0.61/0.77      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C) @ 
% 0.61/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.61/0.77  thf('21', plain,
% 0.61/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf(redefinition_k3_relset_1, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.77       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.61/0.77  thf('22', plain,
% 0.61/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.77         (((k3_relset_1 @ X19 @ X20 @ X18) = (k4_relat_1 @ X18))
% 0.61/0.77          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.61/0.77      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.61/0.77  thf('23', plain,
% 0.61/0.77      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('sup-', [status(thm)], ['21', '22'])).
% 0.61/0.77  thf('24', plain,
% 0.61/0.77      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.61/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.77      inference('demod', [status(thm)], ['20', '23'])).
% 0.61/0.77  thf('25', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.61/0.77  thf('26', plain,
% 0.61/0.77      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.61/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.61/0.77         <= (~
% 0.61/0.77             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.61/0.77               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.61/0.77      inference('split', [status(esa)], ['0'])).
% 0.61/0.77  thf('27', plain,
% 0.61/0.77      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.61/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.61/0.77         <= (~
% 0.61/0.77             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.61/0.77               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.61/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.77  thf('28', plain,
% 0.61/0.77      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.61/0.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.61/0.77      inference('sup-', [status(thm)], ['24', '27'])).
% 0.61/0.77  thf('29', plain,
% 0.61/0.77      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)) | 
% 0.61/0.77       ~
% 0.61/0.77       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.61/0.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 0.61/0.77       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.61/0.77      inference('split', [status(esa)], ['0'])).
% 0.61/0.77  thf('30', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 0.61/0.77      inference('sat_resolution*', [status(thm)], ['17', '28', '29'])).
% 0.61/0.77  thf('31', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A)),
% 0.61/0.77      inference('simpl_trail', [status(thm)], ['10', '30'])).
% 0.61/0.77  thf(d1_funct_2, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.77  thf(zf_stmt_1, axiom,
% 0.61/0.77    (![B:$i,A:$i]:
% 0.61/0.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.77       ( zip_tseitin_0 @ B @ A ) ))).
% 0.61/0.77  thf('32', plain,
% 0.61/0.77      (![X27 : $i, X28 : $i]:
% 0.61/0.77         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.77  thf('33', plain,
% 0.61/0.77      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.61/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.77      inference('demod', [status(thm)], ['20', '23'])).
% 0.61/0.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.61/0.77  thf(zf_stmt_3, axiom,
% 0.61/0.77    (![C:$i,B:$i,A:$i]:
% 0.61/0.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.61/0.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.61/0.77  thf(zf_stmt_5, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.61/0.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.77  thf('34', plain,
% 0.61/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.61/0.77         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.61/0.77          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.61/0.77          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.77  thf('35', plain,
% 0.61/0.77      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B_1)
% 0.61/0.77        | ~ (zip_tseitin_0 @ sk_A @ sk_B_1))),
% 0.61/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.61/0.77  thf('36', plain,
% 0.61/0.77      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.61/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.77      inference('demod', [status(thm)], ['20', '23'])).
% 0.61/0.77  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.77  thf('37', plain,
% 0.61/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.77         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.61/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.61/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.77  thf('38', plain,
% 0.61/0.77      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C))
% 0.61/0.77         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.61/0.77  thf('39', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.61/0.77  thf(t55_funct_1, axiom,
% 0.61/0.77    (![A:$i]:
% 0.61/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.77       ( ( v2_funct_1 @ A ) =>
% 0.61/0.77         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.61/0.77           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.61/0.77  thf('40', plain,
% 0.61/0.77      (![X5 : $i]:
% 0.61/0.77         (~ (v2_funct_1 @ X5)
% 0.61/0.77          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.61/0.77          | ~ (v1_funct_1 @ X5)
% 0.61/0.77          | ~ (v1_relat_1 @ X5))),
% 0.61/0.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.61/0.77  thf('41', plain,
% 0.61/0.77      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_C)
% 0.61/0.77        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.77        | ~ (v2_funct_1 @ sk_C))),
% 0.61/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.61/0.77  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.77  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('44', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('45', plain,
% 0.61/0.77      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.61/0.77      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.61/0.77  thf('46', plain,
% 0.61/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf(redefinition_k2_relset_1, axiom,
% 0.61/0.77    (![A:$i,B:$i,C:$i]:
% 0.61/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.61/0.77  thf('47', plain,
% 0.61/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.61/0.77         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.61/0.77          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.61/0.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.77  thf('48', plain,
% 0.61/0.77      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.61/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.61/0.77  thf('49', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_B_1))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('50', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 0.61/0.77      inference('sup+', [status(thm)], ['48', '49'])).
% 0.61/0.77  thf('51', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.61/0.77      inference('demod', [status(thm)], ['45', '50'])).
% 0.61/0.77  thf('52', plain,
% 0.61/0.77      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C)) = (sk_B_1))),
% 0.61/0.77      inference('demod', [status(thm)], ['38', '51'])).
% 0.61/0.77  thf('53', plain,
% 0.61/0.77      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.61/0.77         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.61/0.77          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.61/0.77          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.77  thf('54', plain,
% 0.61/0.77      ((((sk_B_1) != (sk_B_1))
% 0.61/0.77        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B_1)
% 0.61/0.77        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 0.61/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.61/0.77  thf('55', plain,
% 0.61/0.77      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A)
% 0.61/0.77        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B_1))),
% 0.61/0.77      inference('simplify', [status(thm)], ['54'])).
% 0.61/0.77  thf('56', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A)),
% 0.61/0.77      inference('simpl_trail', [status(thm)], ['10', '30'])).
% 0.61/0.77  thf('57', plain, (~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B_1)),
% 0.61/0.77      inference('clc', [status(thm)], ['55', '56'])).
% 0.61/0.77  thf('58', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B_1)),
% 0.61/0.77      inference('clc', [status(thm)], ['35', '57'])).
% 0.61/0.77  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.61/0.77      inference('sup-', [status(thm)], ['32', '58'])).
% 0.61/0.77  thf('60', plain,
% 0.61/0.77      (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ k1_xboole_0)),
% 0.61/0.77      inference('demod', [status(thm)], ['31', '59'])).
% 0.61/0.77  thf('61', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.61/0.77      inference('demod', [status(thm)], ['45', '50'])).
% 0.61/0.77  thf(t3_funct_2, axiom,
% 0.61/0.77    (![A:$i]:
% 0.61/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.77       ( ( v1_funct_1 @ A ) & 
% 0.61/0.77         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.61/0.77         ( m1_subset_1 @
% 0.61/0.77           A @ 
% 0.61/0.77           ( k1_zfmisc_1 @
% 0.61/0.77             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.61/0.77  thf('62', plain,
% 0.61/0.77      (![X35 : $i]:
% 0.61/0.77         ((v1_funct_2 @ X35 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))
% 0.61/0.77          | ~ (v1_funct_1 @ X35)
% 0.61/0.77          | ~ (v1_relat_1 @ X35))),
% 0.61/0.77      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.61/0.77  thf('63', plain,
% 0.61/0.77      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ 
% 0.61/0.77         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.61/0.77        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.61/0.77        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.61/0.77      inference('sup+', [status(thm)], ['61', '62'])).
% 0.61/0.77  thf('64', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.61/0.77  thf('65', plain,
% 0.61/0.77      (![X5 : $i]:
% 0.61/0.77         (~ (v2_funct_1 @ X5)
% 0.61/0.77          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.61/0.77          | ~ (v1_funct_1 @ X5)
% 0.61/0.77          | ~ (v1_relat_1 @ X5))),
% 0.61/0.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.61/0.77  thf('66', plain,
% 0.61/0.77      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_C)
% 0.61/0.77        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.77        | ~ (v2_funct_1 @ sk_C))),
% 0.61/0.77      inference('sup+', [status(thm)], ['64', '65'])).
% 0.61/0.77  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.77  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('70', plain,
% 0.61/0.77      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.61/0.77      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.61/0.77  thf('71', plain,
% 0.61/0.77      (![X27 : $i, X28 : $i]:
% 0.61/0.77         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.77  thf(rc2_subset_1, axiom,
% 0.61/0.77    (![A:$i]:
% 0.61/0.77     ( ?[B:$i]:
% 0.61/0.77       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.61/0.77  thf('72', plain, (![X1 : $i]: (v1_xboole_0 @ (sk_B @ X1))),
% 0.61/0.77      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.61/0.77  thf('73', plain, (![X1 : $i]: (v1_xboole_0 @ (sk_B @ X1))),
% 0.61/0.77      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.61/0.77  thf(l13_xboole_0, axiom,
% 0.61/0.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.77  thf('74', plain,
% 0.61/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.77  thf('75', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 0.61/0.77      inference('sup-', [status(thm)], ['73', '74'])).
% 0.61/0.77  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.77      inference('demod', [status(thm)], ['72', '75'])).
% 0.61/0.77  thf('77', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.61/0.77      inference('sup+', [status(thm)], ['71', '76'])).
% 0.61/0.77  thf('78', plain,
% 0.61/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('79', plain,
% 0.61/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.61/0.77         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.61/0.77          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.61/0.77          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.77  thf('80', plain,
% 0.61/0.77      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.61/0.77        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.61/0.77      inference('sup-', [status(thm)], ['78', '79'])).
% 0.61/0.77  thf('81', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.61/0.77      inference('sup-', [status(thm)], ['77', '80'])).
% 0.61/0.77  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('83', plain,
% 0.61/0.77      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.61/0.77         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.61/0.77          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.61/0.77          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.77  thf('84', plain,
% 0.61/0.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.61/0.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['82', '83'])).
% 0.61/0.77  thf('85', plain,
% 0.61/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('86', plain,
% 0.61/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.77         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.61/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.61/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.77  thf('87', plain,
% 0.61/0.77      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.61/0.77      inference('sup-', [status(thm)], ['85', '86'])).
% 0.61/0.77  thf('88', plain,
% 0.61/0.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.61/0.77        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.61/0.77      inference('demod', [status(thm)], ['84', '87'])).
% 0.61/0.77  thf('89', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['81', '88'])).
% 0.61/0.77  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 0.61/0.77      inference('sup-', [status(thm)], ['32', '58'])).
% 0.61/0.77  thf('91', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_B_1) | ((k1_xboole_0) = (k1_relat_1 @ sk_C)))),
% 0.61/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.61/0.77  thf('92', plain,
% 0.61/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.77  thf('93', plain,
% 0.61/0.77      (![X27 : $i, X28 : $i]:
% 0.61/0.77         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.77  thf('94', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 0.61/0.77      inference('simplify', [status(thm)], ['93'])).
% 0.61/0.77  thf('95', plain,
% 0.61/0.77      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.77      inference('sup+', [status(thm)], ['92', '94'])).
% 0.61/0.77  thf('96', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B_1)),
% 0.61/0.77      inference('clc', [status(thm)], ['35', '57'])).
% 0.61/0.77  thf('97', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.61/0.77      inference('sup-', [status(thm)], ['95', '96'])).
% 0.61/0.77  thf('98', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C))),
% 0.61/0.77      inference('clc', [status(thm)], ['91', '97'])).
% 0.61/0.77  thf('99', plain, (((k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.61/0.77      inference('demod', [status(thm)], ['70', '98'])).
% 0.61/0.77  thf('100', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.61/0.77  thf('101', plain,
% 0.61/0.77      (![X3 : $i]:
% 0.61/0.77         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.61/0.77          | ~ (v1_funct_1 @ X3)
% 0.61/0.77          | ~ (v1_relat_1 @ X3))),
% 0.61/0.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.61/0.77  thf('102', plain,
% 0.61/0.77      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_C)
% 0.61/0.77        | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.77      inference('sup+', [status(thm)], ['100', '101'])).
% 0.61/0.77  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.77  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('105', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.61/0.77  thf('106', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.61/0.77  thf('107', plain,
% 0.61/0.77      (![X3 : $i]:
% 0.61/0.77         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.61/0.77          | ~ (v1_funct_1 @ X3)
% 0.61/0.77          | ~ (v1_relat_1 @ X3))),
% 0.61/0.77      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.61/0.77  thf('108', plain,
% 0.61/0.77      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_C)
% 0.61/0.77        | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.77      inference('sup+', [status(thm)], ['106', '107'])).
% 0.61/0.77  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.77  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('111', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.61/0.77      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.61/0.77  thf('112', plain,
% 0.61/0.77      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ k1_xboole_0)),
% 0.61/0.77      inference('demod', [status(thm)], ['63', '99', '105', '111'])).
% 0.61/0.77  thf('113', plain, ($false), inference('demod', [status(thm)], ['60', '112'])).
% 0.61/0.77  
% 0.61/0.77  % SZS output end Refutation
% 0.61/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
