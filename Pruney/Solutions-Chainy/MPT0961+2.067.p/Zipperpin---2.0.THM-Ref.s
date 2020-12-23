%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.er0Z8D0ila

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:48 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 708 expanded)
%              Number of leaves         :   27 ( 205 expanded)
%              Depth                    :   17
%              Number of atoms          :  740 (8342 expanded)
%              Number of equality atoms :   63 ( 256 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X6: $i] :
      ( ( r1_tarski @ X6 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X6 ) @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X13
       != ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
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

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','38','39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('44',plain,
    ( ( ( k1_relset_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 @ sk_A )
      = ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 @ sk_A )
    = ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('48',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('52',plain,
    ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X13
       != ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('58',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('59',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','59','60'])).

thf('62',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('63',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','71'])).

thf('73',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['41','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.er0Z8D0ila
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 120 iterations in 0.113s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.57  thf(t3_funct_2, conjecture,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.57       ( ( v1_funct_1 @ A ) & 
% 0.40/0.57         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.40/0.57         ( m1_subset_1 @
% 0.40/0.57           A @ 
% 0.40/0.57           ( k1_zfmisc_1 @
% 0.40/0.57             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i]:
% 0.40/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.57          ( ( v1_funct_1 @ A ) & 
% 0.40/0.57            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.40/0.57            ( m1_subset_1 @
% 0.40/0.57              A @ 
% 0.40/0.57              ( k1_zfmisc_1 @
% 0.40/0.57                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      ((~ (v1_funct_1 @ sk_A)
% 0.40/0.57        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.40/0.57        | ~ (m1_subset_1 @ sk_A @ 
% 0.40/0.57             (k1_zfmisc_1 @ 
% 0.40/0.57              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.40/0.57         <= (~
% 0.40/0.57             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.40/0.57      inference('split', [status(esa)], ['0'])).
% 0.40/0.57  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.40/0.57      inference('split', [status(esa)], ['0'])).
% 0.40/0.57  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.57  thf(t21_relat_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( v1_relat_1 @ A ) =>
% 0.40/0.57       ( r1_tarski @
% 0.40/0.57         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      (![X6 : $i]:
% 0.40/0.57         ((r1_tarski @ X6 @ 
% 0.40/0.57           (k2_zfmisc_1 @ (k1_relat_1 @ X6) @ (k2_relat_1 @ X6)))
% 0.40/0.57          | ~ (v1_relat_1 @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.40/0.57  thf(t3_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (![X3 : $i, X5 : $i]:
% 0.40/0.57         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | (m1_subset_1 @ X0 @ 
% 0.40/0.57             (k1_zfmisc_1 @ 
% 0.40/0.57              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      ((~ (m1_subset_1 @ sk_A @ 
% 0.40/0.57           (k1_zfmisc_1 @ 
% 0.40/0.57            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((m1_subset_1 @ sk_A @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.40/0.57      inference('split', [status(esa)], ['0'])).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      ((~ (v1_relat_1 @ sk_A))
% 0.40/0.57         <= (~
% 0.40/0.57             ((m1_subset_1 @ sk_A @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.57  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('11', plain,
% 0.40/0.57      (((m1_subset_1 @ sk_A @ 
% 0.40/0.57         (k1_zfmisc_1 @ 
% 0.40/0.57          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.40/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.40/0.57       ~
% 0.40/0.57       ((m1_subset_1 @ sk_A @ 
% 0.40/0.57         (k1_zfmisc_1 @ 
% 0.40/0.57          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.40/0.57       ~ ((v1_funct_1 @ sk_A))),
% 0.40/0.57      inference('split', [status(esa)], ['0'])).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.40/0.57      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.40/0.57      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.40/0.57  thf(d1_funct_2, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_1, axiom,
% 0.40/0.57    (![B:$i,A:$i]:
% 0.40/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (![X11 : $i, X12 : $i]:
% 0.40/0.57         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | (m1_subset_1 @ X0 @ 
% 0.40/0.57             (k1_zfmisc_1 @ 
% 0.40/0.57              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.57  thf(zf_stmt_3, axiom,
% 0.40/0.57    (![C:$i,B:$i,A:$i]:
% 0.40/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.57  thf(zf_stmt_5, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.57         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.40/0.57          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.40/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.57          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.40/0.57          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.57          | ~ (v1_relat_1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | (m1_subset_1 @ X0 @ 
% 0.40/0.57             (k1_zfmisc_1 @ 
% 0.40/0.57              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.57         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.40/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.40/0.57              = (k1_relat_1 @ X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.57         (((X13) != (k1_relset_1 @ X13 @ X14 @ X15))
% 0.40/0.57          | (v1_funct_2 @ X15 @ X13 @ X14)
% 0.40/0.57          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.40/0.57          | ~ (v1_relat_1 @ X0)
% 0.40/0.57          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.57          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.57          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.40/0.57          | ~ (v1_relat_1 @ X0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ X0)
% 0.40/0.57          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['19', '25'])).
% 0.40/0.57  thf('27', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.57          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ X0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.40/0.57      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.57  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.40/0.57      inference('demod', [status(thm)], ['14', '31'])).
% 0.40/0.57  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf(t64_relat_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( v1_relat_1 @ A ) =>
% 0.40/0.57       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.57           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.57         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.57  thf('34', plain,
% 0.40/0.57      (![X7 : $i]:
% 0.40/0.57         (((k2_relat_1 @ X7) != (k1_xboole_0))
% 0.40/0.57          | ((X7) = (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ X7))),
% 0.40/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.57  thf('35', plain,
% 0.40/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.57        | ~ (v1_relat_1 @ sk_A)
% 0.40/0.57        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.57  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('37', plain,
% 0.40/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.57  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.57  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.57  thf(t60_relat_1, axiom,
% 0.40/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.57  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.57  thf('41', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.57      inference('demod', [status(thm)], ['32', '38', '39', '40'])).
% 0.40/0.57  thf('42', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('43', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.40/0.57              = (k1_relat_1 @ X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.57  thf('44', plain,
% 0.40/0.57      ((((k1_relset_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0 @ sk_A)
% 0.40/0.57          = (k1_relat_1 @ sk_A))
% 0.40/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.40/0.57  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('46', plain,
% 0.40/0.57      (((k1_relset_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0 @ sk_A)
% 0.40/0.57         = (k1_relat_1 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.40/0.57  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.57  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.57  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.57  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.57  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.57  thf('52', plain,
% 0.40/0.57      (((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 0.40/0.57  thf('53', plain,
% 0.40/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.57         (((X13) != (k1_relset_1 @ X13 @ X14 @ X15))
% 0.40/0.57          | (v1_funct_2 @ X15 @ X13 @ X14)
% 0.40/0.57          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.57  thf('54', plain,
% 0.40/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.57        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.40/0.57        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.40/0.57  thf('55', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('56', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | (m1_subset_1 @ X0 @ 
% 0.40/0.57             (k1_zfmisc_1 @ 
% 0.40/0.57              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.57  thf('57', plain,
% 0.40/0.57      (((m1_subset_1 @ sk_A @ 
% 0.40/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)))
% 0.40/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['55', '56'])).
% 0.40/0.57  thf(t113_zfmisc_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.57  thf('58', plain,
% 0.40/0.57      (![X1 : $i, X2 : $i]:
% 0.40/0.57         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.57  thf('59', plain,
% 0.40/0.57      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['58'])).
% 0.40/0.57  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('61', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['57', '59', '60'])).
% 0.40/0.57  thf('62', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.57  thf('63', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.40/0.57  thf('64', plain,
% 0.40/0.57      (![X1 : $i, X2 : $i]:
% 0.40/0.57         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.57  thf('65', plain,
% 0.40/0.57      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['64'])).
% 0.40/0.57  thf('66', plain,
% 0.40/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.57         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.40/0.57          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.40/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.57  thf('67', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.40/0.57          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.40/0.57          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.40/0.57  thf('68', plain,
% 0.40/0.57      (![X11 : $i, X12 : $i]:
% 0.40/0.57         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.57  thf('69', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 0.40/0.57      inference('simplify', [status(thm)], ['68'])).
% 0.40/0.57  thf('70', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.40/0.57          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['67', '69'])).
% 0.40/0.57  thf('71', plain,
% 0.40/0.57      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.57      inference('sup-', [status(thm)], ['63', '70'])).
% 0.40/0.57  thf('72', plain,
% 0.40/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.57        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['54', '71'])).
% 0.40/0.57  thf('73', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.57      inference('simplify', [status(thm)], ['72'])).
% 0.40/0.57  thf('74', plain, ($false), inference('demod', [status(thm)], ['41', '73'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
