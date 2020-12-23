%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qC0bQWDpKT

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:46 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 307 expanded)
%              Number of leaves         :   31 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  656 (3419 expanded)
%              Number of equality atoms :   48 ( 107 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
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

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( v4_relat_1 @ ( sk_C @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v4_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( sk_C @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('48',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( sk_C @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_funct_2 @ ( sk_C @ X19 @ X20 ) @ X20 @ X19 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['32','38','39','53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qC0bQWDpKT
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 215 iterations in 0.251s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.72  thf(t3_funct_2, conjecture,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v1_funct_1 @ A ) & 
% 0.49/0.72         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.49/0.72         ( m1_subset_1 @
% 0.49/0.72           A @ 
% 0.49/0.72           ( k1_zfmisc_1 @
% 0.49/0.72             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i]:
% 0.49/0.72        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72          ( ( v1_funct_1 @ A ) & 
% 0.49/0.72            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.49/0.72            ( m1_subset_1 @
% 0.49/0.72              A @ 
% 0.49/0.72              ( k1_zfmisc_1 @
% 0.49/0.72                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ sk_A)
% 0.49/0.72        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.49/0.72        | ~ (m1_subset_1 @ sk_A @ 
% 0.49/0.72             (k1_zfmisc_1 @ 
% 0.49/0.72              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf(t21_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( r1_tarski @
% 0.49/0.72         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X6 : $i]:
% 0.49/0.72         ((r1_tarski @ X6 @ 
% 0.49/0.72           (k2_zfmisc_1 @ (k1_relat_1 @ X6) @ (k2_relat_1 @ X6)))
% 0.49/0.72          | ~ (v1_relat_1 @ X6))),
% 0.49/0.72      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.49/0.72  thf(t3_subset, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      (![X1 : $i, X3 : $i]:
% 0.49/0.72         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (m1_subset_1 @ X0 @ 
% 0.49/0.72             (k1_zfmisc_1 @ 
% 0.49/0.72              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      ((~ (m1_subset_1 @ sk_A @ 
% 0.49/0.72           (k1_zfmisc_1 @ 
% 0.49/0.72            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ sk_A @ 
% 0.49/0.72               (k1_zfmisc_1 @ 
% 0.49/0.72                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('9', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_A))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ sk_A @ 
% 0.49/0.72               (k1_zfmisc_1 @ 
% 0.49/0.72                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      (((m1_subset_1 @ sk_A @ 
% 0.49/0.72         (k1_zfmisc_1 @ 
% 0.49/0.72          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.49/0.72       ~
% 0.49/0.72       ((m1_subset_1 @ sk_A @ 
% 0.49/0.72         (k1_zfmisc_1 @ 
% 0.49/0.72          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.49/0.72       ~ ((v1_funct_1 @ sk_A))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.49/0.72  thf(d1_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.49/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.49/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_1, axiom,
% 0.49/0.72    (![B:$i,A:$i]:
% 0.49/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (![X11 : $i, X12 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.72  thf('16', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (m1_subset_1 @ X0 @ 
% 0.49/0.72             (k1_zfmisc_1 @ 
% 0.49/0.72              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.72  thf(zf_stmt_3, axiom,
% 0.49/0.72    (![C:$i,B:$i,A:$i]:
% 0.49/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.49/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.49/0.72  thf(zf_stmt_5, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.49/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.72         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.49/0.72          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.49/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.72          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.72  thf('19', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.49/0.72          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['15', '18'])).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (m1_subset_1 @ X0 @ 
% 0.49/0.72             (k1_zfmisc_1 @ 
% 0.49/0.72              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.72         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.49/0.72          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.49/0.72              = (k1_relat_1 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.72  thf('23', plain,
% 0.49/0.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.49/0.72         (((X13) != (k1_relset_1 @ X13 @ X14 @ X15))
% 0.49/0.72          | (v1_funct_2 @ X15 @ X13 @ X14)
% 0.49/0.72          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.72  thf('24', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.72          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.49/0.72  thf('25', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.72          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['24'])).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['19', '25'])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.72          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.49/0.72  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.73  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.49/0.73      inference('demod', [status(thm)], ['14', '31'])).
% 0.49/0.73  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.49/0.73      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.73  thf(t64_relat_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( v1_relat_1 @ A ) =>
% 0.49/0.73       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.73           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.73         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.73  thf('34', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (((k2_relat_1 @ X7) != (k1_xboole_0))
% 0.49/0.73          | ((X7) = (k1_xboole_0))
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.49/0.73  thf('35', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ~ (v1_relat_1 @ sk_A)
% 0.49/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.73  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('37', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.73      inference('demod', [status(thm)], ['35', '36'])).
% 0.49/0.73  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.73  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.73  thf(rc1_funct_2, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ?[C:$i]:
% 0.49/0.73       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 0.49/0.73         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 0.49/0.73         ( v1_relat_1 @ C ) & 
% 0.49/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.49/0.73  thf('40', plain,
% 0.49/0.73      (![X19 : $i, X20 : $i]: (v4_relat_1 @ (sk_C @ X19 @ X20) @ X20)),
% 0.49/0.73      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.49/0.73  thf(d18_relat_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( v1_relat_1 @ B ) =>
% 0.49/0.73       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.49/0.73  thf('41', plain,
% 0.49/0.73      (![X4 : $i, X5 : $i]:
% 0.49/0.73         (~ (v4_relat_1 @ X4 @ X5)
% 0.49/0.73          | (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.49/0.73          | ~ (v1_relat_1 @ X4))),
% 0.49/0.73      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.49/0.73  thf('42', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.49/0.73          | (r1_tarski @ (k1_relat_1 @ (sk_C @ X1 @ X0)) @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.73  thf('43', plain, (![X19 : $i, X20 : $i]: (v1_relat_1 @ (sk_C @ X19 @ X20))),
% 0.49/0.73      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.49/0.73  thf('44', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k1_relat_1 @ (sk_C @ X1 @ X0)) @ X0)),
% 0.49/0.73      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.73  thf(t3_xboole_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.73  thf('45', plain,
% 0.49/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.49/0.73  thf('46', plain,
% 0.49/0.73      (![X0 : $i]: ((k1_relat_1 @ (sk_C @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.73  thf('47', plain,
% 0.49/0.73      (![X0 : $i]: ((k1_relat_1 @ (sk_C @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.73  thf('48', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.49/0.73          | ((X7) = (k1_xboole_0))
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.49/0.73  thf('49', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73          | ~ (v1_relat_1 @ (sk_C @ X0 @ k1_xboole_0))
% 0.49/0.73          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.73  thf('50', plain, (![X19 : $i, X20 : $i]: (v1_relat_1 @ (sk_C @ X19 @ X20))),
% 0.49/0.73      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.49/0.73  thf('51', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.73      inference('demod', [status(thm)], ['49', '50'])).
% 0.49/0.73  thf('52', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.73  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('demod', [status(thm)], ['46', '52'])).
% 0.49/0.73  thf('54', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.73  thf('55', plain,
% 0.49/0.73      (![X19 : $i, X20 : $i]: (v1_funct_2 @ (sk_C @ X19 @ X20) @ X20 @ X19)),
% 0.49/0.73      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.49/0.73  thf('56', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.49/0.73      inference('sup+', [status(thm)], ['54', '55'])).
% 0.49/0.73  thf('57', plain, ($false),
% 0.49/0.73      inference('demod', [status(thm)], ['32', '38', '39', '53', '56'])).
% 0.49/0.73  
% 0.49/0.73  % SZS output end Refutation
% 0.49/0.73  
% 0.57/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
