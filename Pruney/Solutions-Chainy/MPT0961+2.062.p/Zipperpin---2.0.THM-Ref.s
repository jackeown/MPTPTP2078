%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gXu26VjN8W

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 (1274 expanded)
%              Number of leaves         :   26 ( 363 expanded)
%              Depth                    :   16
%              Number of atoms          :  767 (14987 expanded)
%              Number of equality atoms :   54 ( 413 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['19','24','25'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['16','26'])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_A @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_A @ k1_xboole_0 @ ( k1_relat_1 @ sk_A ) )
    | ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('38',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('42',plain,(
    r1_tarski @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','40','41'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','44','45','46','47'])).

thf('49',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['16','26'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('51',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('54',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ( X21 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('57',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('66',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X20: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58','66'])).

thf('68',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('69',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['55','69','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gXu26VjN8W
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 88 iterations in 0.085s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(d1_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t21_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( r1_tarski @
% 0.20/0.53         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X7 : $i]:
% 0.20/0.53         ((r1_tarski @ X7 @ 
% 0.20/0.53           (k2_zfmisc_1 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X4 : $i, X6 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (m1_subset_1 @ X0 @ 
% 0.20/0.53             (k1_zfmisc_1 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_2, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_4, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.20/0.53          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.53          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (m1_subset_1 @ X0 @ 
% 0.20/0.53             (k1_zfmisc_1 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.20/0.53              = (k1_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.20/0.53          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.20/0.53          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.53          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.53          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.53  thf(t3_funct_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( v1_funct_1 @ A ) & 
% 0.20/0.53         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.53         ( m1_subset_1 @
% 0.20/0.53           A @ 
% 0.20/0.53           ( k1_zfmisc_1 @
% 0.20/0.53             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_5, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53          ( ( v1_funct_1 @ A ) & 
% 0.20/0.53            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.53            ( m1_subset_1 @
% 0.20/0.53              A @ 
% 0.20/0.53              ( k1_zfmisc_1 @
% 0.20/0.53                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((~ (v1_funct_1 @ sk_A)
% 0.20/0.53        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_A @ 
% 0.20/0.53             (k1_zfmisc_1 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['15'])).
% 0.20/0.53  thf('17', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('18', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['15'])).
% 0.20/0.53  thf('19', plain, (((v1_funct_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (m1_subset_1 @ X0 @ 
% 0.20/0.53             (k1_zfmisc_1 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ sk_A @ 
% 0.20/0.53           (k1_zfmisc_1 @ 
% 0.20/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((m1_subset_1 @ sk_A @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.20/0.53      inference('split', [status(esa)], ['15'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_A))
% 0.20/0.53         <= (~
% 0.20/0.53             ((m1_subset_1 @ sk_A @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_A @ 
% 0.20/0.53         (k1_zfmisc_1 @ 
% 0.20/0.53          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.20/0.53       ~
% 0.20/0.53       ((m1_subset_1 @ sk_A @ 
% 0.20/0.53         (k1_zfmisc_1 @ 
% 0.20/0.53          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.20/0.53       ~ ((v1_funct_1 @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['15'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['19', '24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['16', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '27'])).
% 0.20/0.53  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('30', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.53          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((~ (zip_tseitin_1 @ sk_A @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53        | (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((~ (zip_tseitin_1 @ sk_A @ k1_xboole_0 @ (k1_relat_1 @ sk_A))
% 0.20/0.53        | (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.53  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X7 : $i]:
% 0.20/0.53         ((r1_tarski @ X7 @ 
% 0.20/0.53           (k2_zfmisc_1 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf(t113_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('42', plain, ((r1_tarski @ sk_A @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '40', '41'])).
% 0.20/0.53  thf(t3_xboole_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.53  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53           (k1_relat_1 @ k1_xboole_0))
% 0.20/0.53        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '44', '45', '46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['16', '26'])).
% 0.20/0.53  thf('50', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('51', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.53          (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['48', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (((X19) != (k1_xboole_0))
% 0.20/0.53          | ((X20) = (k1_xboole_0))
% 0.20/0.53          | (v1_funct_2 @ X21 @ X20 @ X19)
% 0.20/0.53          | ((X21) != (k1_xboole_0))
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X20 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.20/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ k1_xboole_0)))
% 0.20/0.53          | (v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.20/0.53          | ((X20) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('59', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (m1_subset_1 @ X0 @ 
% 0.20/0.53             (k1_zfmisc_1 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_A @ 
% 0.20/0.53         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('64', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.20/0.53  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('66', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X20 : $i]:
% 0.20/0.53         ((v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.20/0.53          | ((X20) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['57', '58', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.53  thf('69', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.20/0.53          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.53          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.20/0.53          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['75'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.53          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['70', '77'])).
% 0.20/0.53  thf('79', plain, ($false),
% 0.20/0.53      inference('demod', [status(thm)], ['55', '69', '78'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
