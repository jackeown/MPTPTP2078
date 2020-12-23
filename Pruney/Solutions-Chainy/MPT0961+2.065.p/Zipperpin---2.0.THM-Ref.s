%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iWuYLPuzUS

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:47 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 335 expanded)
%              Number of leaves         :   30 ( 109 expanded)
%              Depth                    :   13
%              Number of atoms          :  772 (3730 expanded)
%              Number of equality atoms :   56 ( 139 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X3: $i] :
      ( ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X3 ) @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( X8 = k1_xboole_0 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X14 )
      | ( zip_tseitin_1 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10
       != ( k1_relset_1 @ X10 @ X11 @ X12 ) )
      | ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( zip_tseitin_1 @ X12 @ X11 @ X10 ) ) ),
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
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('41',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('45',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('47',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('49',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X13 != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X14 @ k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_2 @ ( sk_C @ X16 @ X17 ) @ X17 @ X16 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('59',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X14 )
      | ( zip_tseitin_1 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('66',plain,(
    ! [X8: $i] :
      ( zip_tseitin_0 @ X8 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['67'])).

thf('69',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('71',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('72',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('73',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44','69','70','71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['32','38','39','40','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iWuYLPuzUS
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 137 iterations in 0.156s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(t3_funct_2, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v1_funct_1 @ A ) & 
% 0.42/0.61         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.42/0.61         ( m1_subset_1 @
% 0.42/0.61           A @ 
% 0.42/0.61           ( k1_zfmisc_1 @
% 0.42/0.61             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61          ( ( v1_funct_1 @ A ) & 
% 0.42/0.61            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.42/0.61            ( m1_subset_1 @
% 0.42/0.61              A @ 
% 0.42/0.61              ( k1_zfmisc_1 @
% 0.42/0.61                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ sk_A)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.42/0.61        | ~ (m1_subset_1 @ sk_A @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf(t21_relat_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ A ) =>
% 0.42/0.61       ( r1_tarski @
% 0.42/0.61         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X3 : $i]:
% 0.42/0.61         ((r1_tarski @ X3 @ 
% 0.42/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X3) @ (k2_relat_1 @ X3)))
% 0.42/0.61          | ~ (v1_relat_1 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.42/0.61  thf(t3_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X0 : $i, X2 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (m1_subset_1 @ X0 @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      ((~ (m1_subset_1 @ sk_A @ 
% 0.42/0.61           (k1_zfmisc_1 @ 
% 0.42/0.61            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.42/0.61         <= (~
% 0.42/0.61             ((m1_subset_1 @ sk_A @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_A))
% 0.42/0.61         <= (~
% 0.42/0.61             ((m1_subset_1 @ sk_A @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (((m1_subset_1 @ sk_A @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.42/0.61       ~
% 0.42/0.61       ((m1_subset_1 @ sk_A @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.42/0.61       ~ ((v1_funct_1 @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.42/0.61  thf(d1_funct_2, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_1, axiom,
% 0.42/0.61    (![B:$i,A:$i]:
% 0.42/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X8 @ X9) | ((X8) = (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (m1_subset_1 @ X0 @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_3, axiom,
% 0.42/0.61    (![C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_5, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.61         (~ (zip_tseitin_0 @ X13 @ X14)
% 0.42/0.61          | (zip_tseitin_1 @ X15 @ X13 @ X14)
% 0.42/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.42/0.61          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['15', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (m1_subset_1 @ X0 @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.61         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.42/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.61              = (k1_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         (((X10) != (k1_relset_1 @ X10 @ X11 @ X12))
% 0.42/0.61          | (v1_funct_2 @ X12 @ X10 @ X11)
% 0.42/0.61          | ~ (zip_tseitin_1 @ X12 @ X11 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.42/0.61          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.42/0.61          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.42/0.61          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.61  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.42/0.61  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.42/0.61      inference('demod', [status(thm)], ['14', '31'])).
% 0.42/0.61  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.42/0.61  thf(t64_relat_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ A ) =>
% 0.42/0.61       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.61           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.61         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X4 : $i]:
% 0.42/0.61         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.42/0.61          | ((X4) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_A)
% 0.42/0.61        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.61  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.61  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.61  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.61  thf(t60_relat_1, axiom,
% 0.42/0.61    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.42/0.61     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.42/0.61  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.61  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.42/0.61          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.42/0.61          | ~ (v1_relat_1 @ X0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      ((~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.42/0.61           (k1_relat_1 @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.42/0.61        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.42/0.61           (k2_relat_1 @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.61  thf('44', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.61  thf('45', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X0)
% 0.42/0.61          | (m1_subset_1 @ X0 @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))))
% 0.42/0.61        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.42/0.61  thf('48', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.42/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 0.42/0.61        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.42/0.61  thf(rc1_funct_2, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ?[C:$i]:
% 0.42/0.61       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 0.42/0.61         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 0.42/0.61         ( v1_relat_1 @ C ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.42/0.61      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.61         (((X13) != (k1_xboole_0))
% 0.42/0.61          | ((X14) = (k1_xboole_0))
% 0.42/0.61          | ((X15) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_funct_2 @ X15 @ X14 @ X13)
% 0.42/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X15 @ 
% 0.42/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ k1_xboole_0)))
% 0.42/0.61          | ~ (v1_funct_2 @ X15 @ X14 @ k1_xboole_0)
% 0.42/0.61          | ((X15) = (k1_xboole_0))
% 0.42/0.61          | ((X14) = (k1_xboole_0)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['51'])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((X0) = (k1_xboole_0))
% 0.42/0.61          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_funct_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['50', '52'])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]: (v1_funct_2 @ (sk_C @ X16 @ X17) @ X17 @ X16)),
% 0.42/0.61      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((X0) = (k1_xboole_0)) | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('56', plain, (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C @ X16 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('58', plain, (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C @ X16 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.42/0.61  thf('59', plain, (((v1_relat_1 @ k1_xboole_0) | (v1_relat_1 @ k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.42/0.61  thf('61', plain,
% 0.42/0.61      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.42/0.61      inference('demod', [status(thm)], ['49', '60'])).
% 0.42/0.61  thf('62', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.61         (~ (zip_tseitin_0 @ X13 @ X14)
% 0.42/0.61          | (zip_tseitin_1 @ X15 @ X13 @ X14)
% 0.42/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.61  thf('63', plain,
% 0.42/0.61      (((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.42/0.61        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.42/0.61  thf('64', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X8 @ X9) | ((X8) = (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('65', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X8 @ X9) | ((X9) != (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('66', plain, (![X8 : $i]: (zip_tseitin_0 @ X8 @ k1_xboole_0)),
% 0.42/0.61      inference('simplify', [status(thm)], ['65'])).
% 0.42/0.61  thf('67', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.42/0.61      inference('sup+', [status(thm)], ['64', '66'])).
% 0.42/0.61  thf('68', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.42/0.61      inference('eq_fact', [status(thm)], ['67'])).
% 0.42/0.61  thf('69', plain, ((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('demod', [status(thm)], ['63', '68'])).
% 0.42/0.61  thf('70', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.42/0.61  thf('71', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.61  thf('72', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.61  thf('73', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('demod', [status(thm)], ['43', '44', '69', '70', '71', '72'])).
% 0.42/0.61  thf('74', plain, ($false),
% 0.42/0.61      inference('demod', [status(thm)], ['32', '38', '39', '40', '73'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
