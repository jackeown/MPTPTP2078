%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2kpAGXN9me

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 427 expanded)
%              Number of leaves         :   28 ( 132 expanded)
%              Depth                    :   12
%              Number of atoms          :  703 (4878 expanded)
%              Number of equality atoms :   48 ( 144 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','11','12'])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

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

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('34',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) @ sk_A )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['37','39','40','41','42','43'])).

thf('45',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['37','39','40','41','42','43'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('47',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('60',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['56','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['32','44','45','46','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2kpAGXN9me
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.61  % Solved by: fo/fo7.sh
% 0.21/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.61  % done 157 iterations in 0.152s
% 0.21/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.61  % SZS output start Refutation
% 0.21/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.61  thf(t3_funct_2, conjecture,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.61       ( ( v1_funct_1 @ A ) & 
% 0.21/0.61         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.61         ( m1_subset_1 @
% 0.21/0.61           A @ 
% 0.21/0.61           ( k1_zfmisc_1 @
% 0.21/0.61             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.61    (~( ![A:$i]:
% 0.21/0.61        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.61          ( ( v1_funct_1 @ A ) & 
% 0.21/0.61            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.61            ( m1_subset_1 @
% 0.21/0.61              A @ 
% 0.21/0.61              ( k1_zfmisc_1 @
% 0.21/0.61                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.21/0.61    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.21/0.61  thf('0', plain,
% 0.21/0.61      ((~ (v1_funct_1 @ sk_A)
% 0.21/0.61        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.21/0.61        | ~ (m1_subset_1 @ sk_A @ 
% 0.21/0.61             (k1_zfmisc_1 @ 
% 0.21/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('1', plain,
% 0.21/0.61      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.21/0.61         <= (~
% 0.21/0.61             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.21/0.61      inference('split', [status(esa)], ['0'])).
% 0.21/0.61  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.21/0.61      inference('split', [status(esa)], ['0'])).
% 0.21/0.61  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.61  thf(t21_relat_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( v1_relat_1 @ A ) =>
% 0.21/0.61       ( r1_tarski @
% 0.21/0.61         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.61  thf('5', plain,
% 0.21/0.61      (![X12 : $i]:
% 0.21/0.61         ((r1_tarski @ X12 @ 
% 0.21/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.21/0.61          | ~ (v1_relat_1 @ X12))),
% 0.21/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.61  thf(t3_subset, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.61  thf('6', plain,
% 0.21/0.61      (![X7 : $i, X9 : $i]:
% 0.21/0.61         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.61  thf('7', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | (m1_subset_1 @ X0 @ 
% 0.21/0.61             (k1_zfmisc_1 @ 
% 0.21/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.61  thf('8', plain,
% 0.21/0.61      ((~ (m1_subset_1 @ sk_A @ 
% 0.21/0.61           (k1_zfmisc_1 @ 
% 0.21/0.61            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.21/0.61         <= (~
% 0.21/0.61             ((m1_subset_1 @ sk_A @ 
% 0.21/0.61               (k1_zfmisc_1 @ 
% 0.21/0.61                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.21/0.61      inference('split', [status(esa)], ['0'])).
% 0.21/0.61  thf('9', plain,
% 0.21/0.61      ((~ (v1_relat_1 @ sk_A))
% 0.21/0.61         <= (~
% 0.21/0.61             ((m1_subset_1 @ sk_A @ 
% 0.21/0.61               (k1_zfmisc_1 @ 
% 0.21/0.61                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.61  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('11', plain,
% 0.21/0.61      (((m1_subset_1 @ sk_A @ 
% 0.21/0.61         (k1_zfmisc_1 @ 
% 0.21/0.61          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.61  thf('12', plain,
% 0.21/0.61      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.21/0.61       ~
% 0.21/0.61       ((m1_subset_1 @ sk_A @ 
% 0.21/0.61         (k1_zfmisc_1 @ 
% 0.21/0.61          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.21/0.61       ~ ((v1_funct_1 @ sk_A))),
% 0.21/0.61      inference('split', [status(esa)], ['0'])).
% 0.21/0.61  thf('13', plain,
% 0.21/0.61      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.61      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.21/0.61  thf('14', plain,
% 0.21/0.61      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.21/0.61      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.21/0.61  thf(d1_funct_2, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_1, axiom,
% 0.21/0.61    (![B:$i,A:$i]:
% 0.21/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.61  thf('15', plain,
% 0.21/0.61      (![X18 : $i, X19 : $i]:
% 0.21/0.61         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.61  thf('16', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | (m1_subset_1 @ X0 @ 
% 0.21/0.61             (k1_zfmisc_1 @ 
% 0.21/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.61  thf(zf_stmt_3, axiom,
% 0.21/0.61    (![C:$i,B:$i,A:$i]:
% 0.21/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.61  thf(zf_stmt_5, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.61  thf('17', plain,
% 0.21/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.61         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.21/0.61          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.21/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.61  thf('18', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.61          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.61  thf('19', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.61          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.61  thf('20', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | (m1_subset_1 @ X0 @ 
% 0.21/0.61             (k1_zfmisc_1 @ 
% 0.21/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.61  thf('21', plain,
% 0.21/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.61         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.21/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.61  thf('22', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.61              = (k1_relat_1 @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.61  thf('23', plain,
% 0.21/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.61         (((X20) != (k1_relset_1 @ X20 @ X21 @ X22))
% 0.21/0.61          | (v1_funct_2 @ X22 @ X20 @ X21)
% 0.21/0.61          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.61  thf('24', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.61          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.61  thf('25', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.61          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.61  thf('26', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0)
% 0.21/0.61          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.61  thf('27', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.61          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.61          | ~ (v1_relat_1 @ X0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.61  thf('28', plain,
% 0.21/0.61      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.21/0.61      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.21/0.61  thf('29', plain,
% 0.21/0.61      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.61  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.61  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.21/0.61      inference('demod', [status(thm)], ['14', '31'])).
% 0.21/0.61  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.61  thf('34', plain,
% 0.21/0.61      (![X12 : $i]:
% 0.21/0.61         ((r1_tarski @ X12 @ 
% 0.21/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.21/0.61          | ~ (v1_relat_1 @ X12))),
% 0.21/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.61  thf(d10_xboole_0, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.61  thf('35', plain,
% 0.21/0.61      (![X0 : $i, X2 : $i]:
% 0.21/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.61  thf('36', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (v1_relat_1 @ X0)
% 0.21/0.61          | ~ (r1_tarski @ 
% 0.21/0.61               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.21/0.61          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.61  thf('37', plain,
% 0.21/0.61      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0) @ sk_A)
% 0.21/0.61        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) = (sk_A))
% 0.21/0.61        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.61  thf(t113_zfmisc_1, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.61  thf('38', plain,
% 0.21/0.61      (![X5 : $i, X6 : $i]:
% 0.21/0.61         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.21/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.61  thf('39', plain,
% 0.21/0.61      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.61  thf('40', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.61  thf('41', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.61  thf('42', plain,
% 0.21/0.61      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.61  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('44', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.21/0.61  thf('45', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.21/0.61  thf(t60_relat_1, axiom,
% 0.21/0.61    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.61     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.61  thf('46', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.61  thf('47', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.61  thf('48', plain,
% 0.21/0.61      (![X7 : $i, X9 : $i]:
% 0.21/0.61         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.61  thf('49', plain,
% 0.21/0.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.61  thf('50', plain,
% 0.21/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.61         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.21/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.61  thf('51', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.61  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.61  thf('53', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.61  thf('54', plain,
% 0.21/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.61         (((X20) != (k1_relset_1 @ X20 @ X21 @ X22))
% 0.21/0.61          | (v1_funct_2 @ X22 @ X20 @ X21)
% 0.21/0.61          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.61  thf('55', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (((X1) != (k1_xboole_0))
% 0.21/0.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.21/0.61          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.61  thf('56', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.61      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.61  thf('57', plain,
% 0.21/0.61      (![X18 : $i, X19 : $i]:
% 0.21/0.61         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.61  thf('58', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 0.21/0.61      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.61  thf('59', plain,
% 0.21/0.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.61  thf('60', plain,
% 0.21/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.61         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.21/0.61          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.21/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.61  thf('61', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.21/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.61  thf('62', plain,
% 0.21/0.61      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.61      inference('sup-', [status(thm)], ['58', '61'])).
% 0.21/0.61  thf('63', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.61      inference('demod', [status(thm)], ['56', '62'])).
% 0.21/0.61  thf('64', plain, ($false),
% 0.21/0.61      inference('demod', [status(thm)], ['32', '44', '45', '46', '63'])).
% 0.21/0.61  
% 0.21/0.61  % SZS output end Refutation
% 0.21/0.61  
% 0.21/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
