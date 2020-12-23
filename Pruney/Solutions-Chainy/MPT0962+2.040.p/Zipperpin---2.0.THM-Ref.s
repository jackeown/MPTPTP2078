%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5jYxAov0Ag

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:54 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 884 expanded)
%              Number of leaves         :   28 ( 248 expanded)
%              Depth                    :   15
%              Number of atoms          :  632 (10727 expanded)
%              Number of equality atoms :   45 ( 250 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X15 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18
       != ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('27',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('43',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('44',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['37','38','40','41','42','43'])).

thf('45',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ( X23 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('49',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X22: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('53',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('55',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['37','38','40','41','42','43'])).

thf('57',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['37','38','40','41','42','43'])).

thf('58',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('62',plain,(
    ! [X16: $i] :
      ( zip_tseitin_0 @ X16 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['45','59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5jYxAov0Ag
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 145 iterations in 0.134s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(t4_funct_2, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.58       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.40/0.58         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.40/0.58           ( m1_subset_1 @
% 0.40/0.58             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.58          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.40/0.58            ( ( v1_funct_1 @ B ) & 
% 0.40/0.58              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.40/0.58              ( m1_subset_1 @
% 0.40/0.58                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.40/0.58  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d10_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.58  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.40/0.58  thf(t11_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ C ) =>
% 0.40/0.58       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.40/0.58           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.58         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.40/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ X15)
% 0.40/0.58          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.40/0.58          | ~ (v1_relat_1 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | (m1_subset_1 @ X0 @ 
% 0.40/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.40/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (((m1_subset_1 @ sk_B @ 
% 0.40/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '4'])).
% 0.40/0.58  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf(d1_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_2, axiom,
% 0.40/0.58    (![C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_4, axiom,
% 0.40/0.58    (![B:$i,A:$i]:
% 0.40/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.58  thf(zf_stmt_5, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.58         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.40/0.58          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.40/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.40/0.58        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.40/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.58         (((X18) != (k1_relset_1 @ X18 @ X19 @ X20))
% 0.40/0.59          | (v1_funct_2 @ X20 @ X18 @ X19)
% 0.40/0.59          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.40/0.59        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.40/0.59        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.59        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.59        | ~ (m1_subset_1 @ sk_B @ 
% 0.40/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.59         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.59      inference('split', [status(esa)], ['16'])).
% 0.40/0.59  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('19', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.40/0.59      inference('split', [status(esa)], ['16'])).
% 0.40/0.59  thf('20', plain, (((v1_funct_1 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ 
% 0.40/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      ((~ (m1_subset_1 @ sk_B @ 
% 0.40/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ sk_B @ 
% 0.40/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.40/0.59      inference('split', [status(esa)], ['16'])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (((m1_subset_1 @ sk_B @ 
% 0.40/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.40/0.59       ~
% 0.40/0.59       ((m1_subset_1 @ sk_B @ 
% 0.40/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.40/0.59       ~ ((v1_funct_1 @ sk_B))),
% 0.40/0.59      inference('split', [status(esa)], ['16'])).
% 0.40/0.59  thf('25', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)], ['20', '23', '24'])).
% 0.40/0.59  thf('26', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.40/0.59  thf('27', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['15', '26'])).
% 0.40/0.59  thf('28', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['9', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.59  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['9', '27'])).
% 0.40/0.59  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf('32', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['28', '31'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ 
% 0.40/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf(t3_subset, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i]:
% 0.40/0.59         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i]:
% 0.40/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ sk_B)
% 0.40/0.59        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf(t113_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i]:
% 0.40/0.59         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.40/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.59  thf('41', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.40/0.59  thf('44', plain, (((k1_xboole_0) = (sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['37', '38', '40', '41', '42', '43'])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['32', '44'])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.59         (((X21) != (k1_xboole_0))
% 0.40/0.59          | ((X22) = (k1_xboole_0))
% 0.40/0.59          | (v1_funct_2 @ X23 @ X22 @ X21)
% 0.40/0.59          | ((X23) != (k1_xboole_0))
% 0.40/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X22 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.40/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ k1_xboole_0)))
% 0.40/0.59          | (v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0)
% 0.40/0.59          | ((X22) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['46'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.40/0.59  thf('49', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X7 : $i, X9 : $i]:
% 0.40/0.59         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X22 : $i]:
% 0.40/0.59         ((v1_funct_2 @ k1_xboole_0 @ X22 @ k1_xboole_0)
% 0.40/0.59          | ((X22) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.40/0.59  thf('53', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.40/0.59  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf('55', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain, (((k1_xboole_0) = (sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['37', '38', '40', '41', '42', '43'])).
% 0.40/0.59  thf('57', plain, (((k1_xboole_0) = (sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['37', '38', '40', '41', '42', '43'])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.40/0.59  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['52', '58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X16 @ X17) | ((X17) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.59  thf('62', plain, (![X16 : $i]: (zip_tseitin_0 @ X16 @ k1_xboole_0)),
% 0.40/0.59      inference('simplify', [status(thm)], ['61'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.40/0.59      inference('sup+', [status(thm)], ['60', '62'])).
% 0.40/0.59  thf('64', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.40/0.59      inference('eq_fact', [status(thm)], ['63'])).
% 0.40/0.59  thf('65', plain, ($false),
% 0.40/0.59      inference('demod', [status(thm)], ['45', '59', '64'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
