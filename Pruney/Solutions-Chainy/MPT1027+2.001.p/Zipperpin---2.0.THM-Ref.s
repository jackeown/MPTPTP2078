%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qKRyhnwkRZ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:55 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 198 expanded)
%              Number of leaves         :   39 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  690 (1974 expanded)
%              Number of equality atoms :   41 (  91 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['8','11','12'])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['5','13'])).

thf('15',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( v1_xboole_0 @ ( sk_B @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('21',plain,(
    ! [X6: $i] :
      ( v1_xboole_0 @ ( sk_B @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['34','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('60',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X31 ) ) )
      | ( v1_partfun1 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('61',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('63',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_partfun1 @ X26 @ X27 )
      | ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('64',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['5','13'])).

thf('68',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['18','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['15','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qKRyhnwkRZ
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 240 iterations in 0.118s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(t130_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.38/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.57        ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.38/0.57            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.38/0.57  thf('0', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d1_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_1, axiom,
% 0.38/0.57    (![C:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.57         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 0.38/0.57          | (v1_funct_2 @ X36 @ X34 @ X35)
% 0.38/0.57          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      ((((sk_A) != (sk_A))
% 0.38/0.57        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.38/0.57        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.38/0.57        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.38/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.38/0.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))
% 0.38/0.57         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('split', [status(esa)], ['4'])).
% 0.38/0.57  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('7', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.38/0.57      inference('split', [status(esa)], ['4'])).
% 0.38/0.57  thf('8', plain, (((v1_funct_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((m1_subset_1 @ sk_C @ 
% 0.38/0.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))),
% 0.38/0.57      inference('split', [status(esa)], ['4'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)) | 
% 0.38/0.57       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))) | 
% 0.38/0.57       ~ ((v1_funct_1 @ sk_C))),
% 0.38/0.57      inference('split', [status(esa)], ['4'])).
% 0.38/0.57  thf('13', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['8', '11', '12'])).
% 0.38/0.57  thf('14', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '13'])).
% 0.38/0.57  thf('15', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['3', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_4, axiom,
% 0.38/0.57    (![B:$i,A:$i]:
% 0.38/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.57  thf(zf_stmt_5, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.57         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.38/0.57          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.38/0.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.38/0.57        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X32 : $i, X33 : $i]:
% 0.38/0.57         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.57  thf(rc2_subset_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ?[B:$i]:
% 0.38/0.57       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.38/0.57  thf('20', plain, (![X6 : $i]: (v1_xboole_0 @ (sk_B @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.38/0.57  thf('21', plain, (![X6 : $i]: (v1_xboole_0 @ (sk_B @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.38/0.57  thf(l13_xboole_0, axiom,
% 0.38/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('23', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['19', '24'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc4_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.38/0.57           ( v1_xboole_0 @ C ) ) ) ))).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ X20)
% 0.38/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 0.38/0.57          | (v1_xboole_0 @ X21))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.38/0.57  thf('28', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.57         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.38/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('34', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.38/0.57  thf('37', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.38/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf(cc2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.57         ((v4_relat_1 @ X17 @ X18)
% 0.38/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.57  thf('40', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.38/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.57  thf(t209_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i]:
% 0.38/0.57         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.38/0.57          | ~ (v4_relat_1 @ X8 @ X9)
% 0.38/0.57          | ~ (v1_relat_1 @ X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.57          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.38/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf(cc1_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( v1_relat_1 @ C ) ))).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         ((v1_relat_1 @ X14)
% 0.38/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.57  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['42', '45'])).
% 0.38/0.57  thf(t95_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.57         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i]:
% 0.38/0.57         (((k7_relat_1 @ X10 @ X11) != (k1_xboole_0))
% 0.38/0.57          | (r1_xboole_0 @ (k1_relat_1 @ X10) @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.57          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.57  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.57          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (![X0 : $i]: (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.38/0.57      inference('simplify', [status(thm)], ['50'])).
% 0.38/0.57  thf(t66_xboole_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.38/0.57       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.38/0.57  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['35', '53'])).
% 0.38/0.57  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '23'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['54', '55'])).
% 0.38/0.57  thf('57', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 0.38/0.57      inference('sup+', [status(thm)], ['34', '56'])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '57'])).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc1_partfun1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ X29)
% 0.38/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X31)))
% 0.38/0.57          | (v1_partfun1 @ X30 @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.38/0.57  thf('61', plain, (((v1_partfun1 @ sk_C @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.57  thf('62', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc1_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.38/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.38/0.57  thf('63', plain,
% 0.38/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.57         (~ (v1_funct_1 @ X26)
% 0.38/0.57          | ~ (v1_partfun1 @ X26 @ X27)
% 0.38/0.57          | (v1_funct_2 @ X26 @ X27 @ X28)
% 0.38/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.38/0.57        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.57  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1) | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.38/0.57  thf('67', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '13'])).
% 0.38/0.57  thf('68', plain, (~ (v1_partfun1 @ sk_C @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['66', '67'])).
% 0.38/0.57  thf('69', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['61', '68'])).
% 0.38/0.57  thf('70', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.38/0.57      inference('sup-', [status(thm)], ['58', '69'])).
% 0.38/0.57  thf('71', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '70'])).
% 0.38/0.57  thf('72', plain, ($false), inference('demod', [status(thm)], ['15', '71'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
