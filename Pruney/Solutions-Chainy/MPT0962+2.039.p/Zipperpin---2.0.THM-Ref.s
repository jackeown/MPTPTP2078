%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aUxvkxDCrh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   98 (1021 expanded)
%              Number of leaves         :   30 ( 304 expanded)
%              Depth                    :   16
%              Number of atoms          :  659 (11813 expanded)
%              Number of equality atoms :   44 ( 188 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','26','27'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','29'])).

thf('31',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','30'])).

thf('34',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('45',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['38','39','41','42','43','44'])).

thf('46',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ( X27 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('50',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X26: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49','52'])).

thf('54',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','28'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('56',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['38','39','41','42','43','44'])).

thf('58',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['38','39','41','42','43','44'])).

thf('59',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('63',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['46','60','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aUxvkxDCrh
% 0.15/0.37  % Computer   : n002.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:40:52 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 202 iterations in 0.160s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.65  thf(t4_funct_2, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.65         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.46/0.65           ( m1_subset_1 @
% 0.46/0.65             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.65            ( ( v1_funct_1 @ B ) & 
% 0.46/0.65              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.46/0.65              ( m1_subset_1 @
% 0.46/0.65                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.46/0.65  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t118_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) =>
% 0.46/0.65       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.46/0.65         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X10 @ X11)
% 0.46/0.65          | (r1_tarski @ (k2_zfmisc_1 @ X12 @ X10) @ (k2_zfmisc_1 @ X12 @ X11)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 0.46/0.65          (k2_zfmisc_1 @ X0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf(t21_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( r1_tarski @
% 0.46/0.65         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X16 : $i]:
% 0.46/0.65         ((r1_tarski @ X16 @ 
% 0.46/0.65           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.46/0.65          | ~ (v1_relat_1 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.46/0.65  thf(t1_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.65       ( r1_tarski @ A @ C ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.65          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.65          | (r1_tarski @ X3 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | (r1_tarski @ X0 @ X1)
% 0.46/0.65          | ~ (r1_tarski @ 
% 0.46/0.65               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '5'])).
% 0.46/0.65  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(t3_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X13 : $i, X15 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B @ 
% 0.46/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(d1_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_2, axiom,
% 0.46/0.65    (![C:$i,B:$i,A:$i]:
% 0.46/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_4, axiom,
% 0.46/0.65    (![B:$i,A:$i]:
% 0.46/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.65  thf(zf_stmt_5, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.46/0.65          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.46/0.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.46/0.65        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B @ 
% 0.46/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.46/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.65         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.46/0.65          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.46/0.65          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.46/0.65        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.46/0.65        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.46/0.65        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ sk_B)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_B @ 
% 0.46/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.46/0.65         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['19'])).
% 0.46/0.65  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['19'])).
% 0.46/0.65  thf('23', plain, (((v1_funct_1 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B @ 
% 0.46/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      ((~ (m1_subset_1 @ sk_B @ 
% 0.46/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.46/0.65         <= (~
% 0.46/0.65             ((m1_subset_1 @ sk_B @ 
% 0.46/0.65               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.46/0.65      inference('split', [status(esa)], ['19'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_B @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.46/0.65       ~
% 0.46/0.65       ((m1_subset_1 @ sk_B @ 
% 0.46/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.46/0.65       ~ ((v1_funct_1 @ sk_B))),
% 0.46/0.65      inference('split', [status(esa)], ['19'])).
% 0.46/0.65  thf('28', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['23', '26', '27'])).
% 0.46/0.65  thf('29', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['20', '28'])).
% 0.46/0.65  thf('30', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.46/0.65      inference('clc', [status(thm)], ['18', '29'])).
% 0.46/0.65  thf('31', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.46/0.65      inference('clc', [status(thm)], ['12', '30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.65  thf('33', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.46/0.65      inference('clc', [status(thm)], ['12', '30'])).
% 0.46/0.65  thf('34', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['31', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(d10_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i, X2 : $i]:
% 0.46/0.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ sk_B)
% 0.46/0.65        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf(t113_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.65  thf('42', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.65  thf('45', plain, (((k1_xboole_0) = (sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['38', '39', '41', '42', '43', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['35', '45'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         (((X25) != (k1_xboole_0))
% 0.46/0.65          | ((X26) = (k1_xboole_0))
% 0.46/0.65          | (v1_funct_2 @ X27 @ X26 @ X25)
% 0.46/0.65          | ((X27) != (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X26 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.46/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ k1_xboole_0)))
% 0.46/0.65          | (v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0)
% 0.46/0.65          | ((X26) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.65  thf('50', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X13 : $i, X15 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X26 : $i]:
% 0.46/0.65         ((v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0)
% 0.46/0.65          | ((X26) = (k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['48', '49', '52'])).
% 0.46/0.65  thf('54', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['20', '28'])).
% 0.46/0.65  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('56', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('57', plain, (((k1_xboole_0) = (sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['38', '39', '41', '42', '43', '44'])).
% 0.46/0.65  thf('58', plain, (((k1_xboole_0) = (sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['38', '39', '41', '42', '43', '44'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.46/0.65  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.65  thf('63', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.46/0.65      inference('sup+', [status(thm)], ['61', '63'])).
% 0.46/0.65  thf('65', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.46/0.65      inference('eq_fact', [status(thm)], ['64'])).
% 0.46/0.65  thf('66', plain, ($false),
% 0.46/0.65      inference('demod', [status(thm)], ['46', '60', '65'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
