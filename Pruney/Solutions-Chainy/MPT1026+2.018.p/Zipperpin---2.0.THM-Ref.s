%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QdhfoHWH0U

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:54 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  116 (1040 expanded)
%              Number of leaves         :   40 ( 306 expanded)
%              Depth                    :   21
%              Number of atoms          :  729 (11632 expanded)
%              Number of equality atoms :   48 ( 497 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( zip_tseitin_2 @ ( sk_E_1 @ X36 @ X33 @ X34 ) @ X36 @ X33 @ X34 )
      | ( X35
       != ( k1_funct_2 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('2',plain,(
    ! [X33: $i,X34: $i,X36: $i] :
      ( ( zip_tseitin_2 @ ( sk_E_1 @ X36 @ X33 @ X34 ) @ X36 @ X33 @ X34 )
      | ~ ( r2_hidden @ X36 @ ( k1_funct_2 @ X34 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    zip_tseitin_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    zip_tseitin_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','2'])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X26 )
      | ~ ( zip_tseitin_2 @ X26 @ X28 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,
    ( sk_C
    = ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ~ ( zip_tseitin_2 @ X26 @ X28 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X17 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','6'])).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X26 )
        = X29 )
      | ~ ( zip_tseitin_2 @ X26 @ X28 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','6'])).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( zip_tseitin_2 @ X26 @ X28 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','17','20'])).

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

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','17','20'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','6'])).

thf('35',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_funct_1 @ X26 )
      | ~ ( zip_tseitin_2 @ X26 @ X28 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','17','20'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['38','41','42'])).

thf('44',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['33','43'])).

thf('45',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['31','44'])).

thf('46',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['23','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('48',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['23','45'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','17','20'])).

thf('52',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','54'])).

thf('56',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('65',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('71',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['50','68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QdhfoHWH0U
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:09:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 152 iterations in 0.135s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.38/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.38/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(t121_funct_2, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.60       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.60        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.60          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.38/0.60  thf('0', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(d2_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.60           ( ?[E:$i]:
% 0.38/0.60             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.38/0.60               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.38/0.60               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_2, axiom,
% 0.38/0.60    (![E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_2 @ E @ D @ B @ A ) <=>
% 0.38/0.60       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.38/0.60         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.38/0.60         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.38/0.60  thf(zf_stmt_3, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.60           ( ?[E:$i]: ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) ) ))).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X36 @ X35)
% 0.38/0.60          | (zip_tseitin_2 @ (sk_E_1 @ X36 @ X33 @ X34) @ X36 @ X33 @ X34)
% 0.38/0.60          | ((X35) != (k1_funct_2 @ X34 @ X33)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X33 : $i, X34 : $i, X36 : $i]:
% 0.38/0.60         ((zip_tseitin_2 @ (sk_E_1 @ X36 @ X33 @ X34) @ X36 @ X33 @ X34)
% 0.38/0.60          | ~ (r2_hidden @ X36 @ (k1_funct_2 @ X34 @ X33)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      ((zip_tseitin_2 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A)),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '2'])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      ((zip_tseitin_2 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A)),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '2'])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         (((X28) = (X26)) | ~ (zip_tseitin_2 @ X26 @ X28 @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('6', plain, (((sk_C) = (sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.60  thf('7', plain, ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '6'])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         ((r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.38/0.60          | ~ (zip_tseitin_2 @ X26 @ X28 @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.60  thf(d10_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.60  thf(t11_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ C ) =>
% 0.38/0.60       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.38/0.60           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.38/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.38/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ X17)
% 0.38/0.60          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.38/0.60          | ~ (v1_relat_1 @ X15))),
% 0.38/0.60      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | (m1_subset_1 @ X0 @ 
% 0.38/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.38/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_C @ 
% 0.38/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 0.38/0.60        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '13'])).
% 0.38/0.60  thf('15', plain, ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '6'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         (((k1_relat_1 @ X26) = (X29))
% 0.38/0.60          | ~ (zip_tseitin_2 @ X26 @ X28 @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('17', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('18', plain, ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '6'])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         ((v1_relat_1 @ X26) | ~ (zip_tseitin_2 @ X26 @ X28 @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['14', '17', '20'])).
% 0.38/0.60  thf(d1_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_5, axiom,
% 0.38/0.60    (![C:$i,B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_7, axiom,
% 0.38/0.60    (![B:$i,A:$i]:
% 0.38/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.60  thf(zf_stmt_8, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.60         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.38/0.60          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.38/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['14', '17', '20'])).
% 0.38/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.60         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('28', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.60         (((X20) != (k1_relset_1 @ X20 @ X21 @ X22))
% 0.38/0.60          | (v1_funct_2 @ X22 @ X20 @ X21)
% 0.38/0.60          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      ((((sk_A) != (sk_A))
% 0.38/0.60        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.38/0.60        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.38/0.60      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.38/0.60         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('34', plain, ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '6'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         ((v1_funct_1 @ X26) | ~ (zip_tseitin_2 @ X26 @ X28 @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.60  thf('37', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('38', plain, (((v1_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['14', '17', '20'])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.38/0.60       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.38/0.60       ~ ((v1_funct_1 @ sk_C))),
% 0.38/0.60      inference('split', [status(esa)], ['32'])).
% 0.38/0.60  thf('43', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['38', '41', '42'])).
% 0.38/0.60  thf('44', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['33', '43'])).
% 0.38/0.60  thf('45', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.38/0.60      inference('clc', [status(thm)], ['31', '44'])).
% 0.38/0.60  thf('46', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.38/0.60      inference('clc', [status(thm)], ['23', '45'])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.60  thf('48', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.38/0.60      inference('clc', [status(thm)], ['23', '45'])).
% 0.38/0.60  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.60  thf('50', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['46', '49'])).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['14', '17', '20'])).
% 0.38/0.60  thf('52', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.60  thf(t113_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i]:
% 0.38/0.60         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.60  thf('55', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['51', '52', '54'])).
% 0.38/0.60  thf('56', plain,
% 0.38/0.60      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.60  thf(cc2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.60  thf('57', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.60         ((v4_relat_1 @ X9 @ X10)
% 0.38/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('58', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.38/0.60          | (v4_relat_1 @ X1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.60  thf('59', plain, (![X0 : $i]: (v4_relat_1 @ sk_C @ X0)),
% 0.38/0.60      inference('sup-', [status(thm)], ['55', '58'])).
% 0.38/0.60  thf(d18_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.60  thf('60', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i]:
% 0.38/0.60         (~ (v4_relat_1 @ X7 @ X8)
% 0.38/0.60          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.38/0.60          | ~ (v1_relat_1 @ X7))),
% 0.38/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.60  thf('61', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.60  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf('63', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('64', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.38/0.60      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.38/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.60  thf('65', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.38/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.60  thf('66', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i]:
% 0.38/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('67', plain,
% 0.38/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.60  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['64', '67'])).
% 0.38/0.60  thf('69', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.60  thf('70', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.60  thf('71', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 0.38/0.60      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.60  thf('72', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.38/0.60      inference('sup+', [status(thm)], ['69', '71'])).
% 0.38/0.60  thf('73', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.38/0.60      inference('eq_fact', [status(thm)], ['72'])).
% 0.38/0.60  thf('74', plain, ($false),
% 0.38/0.60      inference('demod', [status(thm)], ['50', '68', '73'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
