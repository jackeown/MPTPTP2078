%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OOuXP3nf7L

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:42 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 180 expanded)
%              Number of leaves         :   30 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  747 (1841 expanded)
%              Number of equality atoms :   35 (  52 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X15: $i] :
      ( zip_tseitin_0 @ X15 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( r1_tarski @ X8 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

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

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('36',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['36','41','42'])).

thf('44',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['33','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['33','43'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['47','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OOuXP3nf7L
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 476 iterations in 0.333s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.78  thf(fc10_relat_1, axiom,
% 0.59/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (![X7 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X7)) | ~ (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.59/0.78  thf(l13_xboole_0, axiom,
% 0.59/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X7 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X7)) | ~ (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.78  thf(t21_relat_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ A ) =>
% 0.59/0.78       ( r1_tarski @
% 0.59/0.78         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X8 : $i]:
% 0.59/0.78         ((r1_tarski @ X8 @ 
% 0.59/0.78           (k2_zfmisc_1 @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X8)))
% 0.59/0.78          | ~ (v1_relat_1 @ X8))),
% 0.59/0.78      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_tarski @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ X0)))
% 0.59/0.78          | ~ (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['4', '5'])).
% 0.59/0.78  thf(t113_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (![X2 : $i, X3 : $i]:
% 0.59/0.78         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.78  thf('8', plain,
% 0.59/0.78      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['7'])).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.59/0.78          | ~ (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '8'])).
% 0.59/0.78  thf(t3_subset, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (![X4 : $i, X6 : $i]:
% 0.59/0.78         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_xboole_0 @ X0)
% 0.59/0.78          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['7'])).
% 0.59/0.78  thf(d1_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.59/0.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.59/0.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.78  thf(zf_stmt_1, axiom,
% 0.59/0.78    (![C:$i,B:$i,A:$i]:
% 0.59/0.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.78  thf(zf_stmt_3, axiom,
% 0.59/0.78    (![B:$i,A:$i]:
% 0.59/0.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.78       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.78  thf(zf_stmt_4, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.59/0.78         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.59/0.78          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.59/0.78          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.59/0.78          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.59/0.78          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((zip_tseitin_0 @ X15 @ X16) | ((X16) != (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.78  thf('16', plain, (![X15 : $i]: (zip_tseitin_0 @ X15 @ k1_xboole_0)),
% 0.59/0.78      inference('simplify', [status(thm)], ['15'])).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.59/0.78          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['14', '16'])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | (zip_tseitin_1 @ X0 @ X1 @ k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '17'])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((zip_tseitin_1 @ X2 @ X1 @ X0)
% 0.59/0.78          | ~ (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X2)
% 0.59/0.78          | ~ (v1_xboole_0 @ X2))),
% 0.59/0.78      inference('sup+', [status(thm)], ['1', '18'])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X8 : $i]:
% 0.59/0.78         ((r1_tarski @ X8 @ 
% 0.59/0.78           (k2_zfmisc_1 @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X8)))
% 0.59/0.78          | ~ (v1_relat_1 @ X8))),
% 0.59/0.78      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X4 : $i, X6 : $i]:
% 0.59/0.78         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | (m1_subset_1 @ X0 @ 
% 0.59/0.78             (k1_zfmisc_1 @ 
% 0.59/0.78              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.78         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.59/0.78          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.59/0.78              = (k1_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         (((X17) != (k1_relset_1 @ X17 @ X18 @ X19))
% 0.59/0.78          | (v1_funct_2 @ X19 @ X17 @ X18)
% 0.59/0.78          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.59/0.78          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.59/0.78          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['19', '27'])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['28'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['0', '29'])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['30'])).
% 0.59/0.78  thf(t3_funct_2, conjecture,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.78       ( ( v1_funct_1 @ A ) & 
% 0.59/0.78         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.59/0.78         ( m1_subset_1 @
% 0.59/0.78           A @ 
% 0.59/0.78           ( k1_zfmisc_1 @
% 0.59/0.78             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_5, negated_conjecture,
% 0.59/0.78    (~( ![A:$i]:
% 0.59/0.78        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.78          ( ( v1_funct_1 @ A ) & 
% 0.59/0.78            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.59/0.78            ( m1_subset_1 @
% 0.59/0.78              A @ 
% 0.59/0.78              ( k1_zfmisc_1 @
% 0.59/0.78                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_A)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.59/0.78        | ~ (m1_subset_1 @ sk_A @ 
% 0.59/0.78             (k1_zfmisc_1 @ 
% 0.59/0.78              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['32'])).
% 0.59/0.78  thf('34', plain, ((v1_funct_1 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.78  thf('35', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.59/0.78      inference('split', [status(esa)], ['32'])).
% 0.59/0.78  thf('36', plain, (((v1_funct_1 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | (m1_subset_1 @ X0 @ 
% 0.59/0.78             (k1_zfmisc_1 @ 
% 0.59/0.78              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_A @ 
% 0.59/0.78           (k1_zfmisc_1 @ 
% 0.59/0.78            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.59/0.78         <= (~
% 0.59/0.78             ((m1_subset_1 @ sk_A @ 
% 0.59/0.78               (k1_zfmisc_1 @ 
% 0.59/0.78                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.59/0.78      inference('split', [status(esa)], ['32'])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      ((~ (v1_relat_1 @ sk_A))
% 0.59/0.78         <= (~
% 0.59/0.78             ((m1_subset_1 @ sk_A @ 
% 0.59/0.78               (k1_zfmisc_1 @ 
% 0.59/0.78                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.78  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (((m1_subset_1 @ sk_A @ 
% 0.59/0.78         (k1_zfmisc_1 @ 
% 0.59/0.78          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['39', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.59/0.78       ~
% 0.59/0.78       ((m1_subset_1 @ sk_A @ 
% 0.59/0.78         (k1_zfmisc_1 @ 
% 0.59/0.78          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.59/0.78       ~ ((v1_funct_1 @ sk_A))),
% 0.59/0.78      inference('split', [status(esa)], ['32'])).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['36', '41', '42'])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['33', '43'])).
% 0.59/0.78  thf('45', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_relat_1 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['31', '44'])).
% 0.59/0.78  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.78  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.78      inference('demod', [status(thm)], ['45', '46'])).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | (m1_subset_1 @ X0 @ 
% 0.59/0.78             (k1_zfmisc_1 @ 
% 0.59/0.78              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.59/0.78         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.59/0.78          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.59/0.78          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.59/0.78          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['49', '50'])).
% 0.59/0.78  thf('52', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.59/0.78          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['48', '51'])).
% 0.59/0.78  thf('53', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.59/0.78          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.78  thf('54', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.59/0.78          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['54'])).
% 0.59/0.78  thf('56', plain,
% 0.59/0.78      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['33', '43'])).
% 0.59/0.78  thf('57', plain,
% 0.59/0.78      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['55', '56'])).
% 0.59/0.78  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.78  thf('59', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.78  thf('60', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | (m1_subset_1 @ X0 @ 
% 0.59/0.78             (k1_zfmisc_1 @ 
% 0.59/0.78              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf(cc4_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_xboole_0 @ A ) =>
% 0.59/0.78       ( ![C:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.59/0.78           ( v1_xboole_0 @ C ) ) ) ))).
% 0.59/0.78  thf('61', plain,
% 0.59/0.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X9)
% 0.59/0.78          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 0.59/0.78          | (v1_xboole_0 @ X10))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.59/0.78  thf('62', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.78  thf('63', plain,
% 0.59/0.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | ~ (v1_relat_1 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['59', '62'])).
% 0.59/0.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.78  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.78  thf('66', plain, ((v1_xboole_0 @ sk_A)),
% 0.59/0.78      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.59/0.78  thf('67', plain, ($false), inference('demod', [status(thm)], ['47', '66'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
