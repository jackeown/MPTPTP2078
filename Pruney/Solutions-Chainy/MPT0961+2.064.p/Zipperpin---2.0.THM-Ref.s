%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Otny7EcDV

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:47 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 298 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  687 (3286 expanded)
%              Number of equality atoms :   54 ( 124 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
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
    ! [X11: $i] :
      ( ( ( k2_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['32','38','39','47','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Otny7EcDV
% 0.13/0.36  % Computer   : n002.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:04:22 EST 2020
% 0.21/0.37  % CPUTime    : 
% 0.21/0.37  % Running portfolio for 600 s
% 0.21/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.37  % Number of cores: 8
% 0.21/0.37  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 215 iterations in 0.219s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.49/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.49/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.70  thf(t3_funct_2, conjecture,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70       ( ( v1_funct_1 @ A ) & 
% 0.49/0.70         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.49/0.70         ( m1_subset_1 @
% 0.49/0.70           A @ 
% 0.49/0.70           ( k1_zfmisc_1 @
% 0.49/0.70             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i]:
% 0.49/0.70        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70          ( ( v1_funct_1 @ A ) & 
% 0.49/0.70            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.49/0.70            ( m1_subset_1 @
% 0.49/0.70              A @ 
% 0.49/0.70              ( k1_zfmisc_1 @
% 0.49/0.70                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.49/0.70  thf('0', plain,
% 0.49/0.70      ((~ (v1_funct_1 @ sk_A)
% 0.49/0.70        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.49/0.70        | ~ (m1_subset_1 @ sk_A @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.49/0.70         <= (~
% 0.49/0.70             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.49/0.70      inference('split', [status(esa)], ['0'])).
% 0.49/0.70  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.49/0.70      inference('split', [status(esa)], ['0'])).
% 0.49/0.70  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.70  thf(t21_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( r1_tarski @
% 0.49/0.70         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      (![X10 : $i]:
% 0.49/0.70         ((r1_tarski @ X10 @ 
% 0.49/0.70           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.49/0.70          | ~ (v1_relat_1 @ X10))),
% 0.49/0.70      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.49/0.70  thf(t3_subset, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      (![X4 : $i, X6 : $i]:
% 0.49/0.70         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.49/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.70  thf('7', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ X0 @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      ((~ (m1_subset_1 @ sk_A @ 
% 0.49/0.70           (k1_zfmisc_1 @ 
% 0.49/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.49/0.70         <= (~
% 0.49/0.70             ((m1_subset_1 @ sk_A @ 
% 0.49/0.70               (k1_zfmisc_1 @ 
% 0.49/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.49/0.70      inference('split', [status(esa)], ['0'])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ sk_A))
% 0.49/0.70         <= (~
% 0.49/0.70             ((m1_subset_1 @ sk_A @ 
% 0.49/0.70               (k1_zfmisc_1 @ 
% 0.49/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.70  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('11', plain,
% 0.49/0.70      (((m1_subset_1 @ sk_A @ 
% 0.49/0.70         (k1_zfmisc_1 @ 
% 0.49/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.49/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.49/0.70  thf('12', plain,
% 0.49/0.70      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.49/0.70       ~
% 0.49/0.70       ((m1_subset_1 @ sk_A @ 
% 0.49/0.70         (k1_zfmisc_1 @ 
% 0.49/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.49/0.70       ~ ((v1_funct_1 @ sk_A))),
% 0.49/0.70      inference('split', [status(esa)], ['0'])).
% 0.49/0.70  thf('13', plain,
% 0.49/0.70      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.49/0.70      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.49/0.70  thf('14', plain,
% 0.49/0.70      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.49/0.70      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.49/0.70  thf(d1_funct_2, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.49/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.49/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_1, axiom,
% 0.49/0.70    (![B:$i,A:$i]:
% 0.49/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.49/0.70  thf('15', plain,
% 0.49/0.70      (![X19 : $i, X20 : $i]:
% 0.49/0.70         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.70  thf('16', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ X0 @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.70  thf(zf_stmt_3, axiom,
% 0.49/0.70    (![C:$i,B:$i,A:$i]:
% 0.49/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.49/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.49/0.70  thf(zf_stmt_5, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.49/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.49/0.70  thf('17', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.49/0.70         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.49/0.70          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.49/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.70          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.70  thf('19', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.49/0.70          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['15', '18'])).
% 0.49/0.70  thf('20', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | (m1_subset_1 @ X0 @ 
% 0.49/0.70             (k1_zfmisc_1 @ 
% 0.49/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.70  thf('21', plain,
% 0.49/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.70         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.49/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.49/0.70              = (k1_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.70         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 0.49/0.70          | (v1_funct_2 @ X23 @ X21 @ X22)
% 0.49/0.70          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.49/0.70  thf('25', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.70          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['24'])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['19', '25'])).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.70          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.49/0.70          | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.70  thf('28', plain,
% 0.49/0.70      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.49/0.70      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.49/0.70  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.70  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.49/0.70      inference('demod', [status(thm)], ['14', '31'])).
% 0.49/0.70  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.70  thf(t64_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.70           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (![X11 : $i]:
% 0.49/0.70         (((k2_relat_1 @ X11) != (k1_xboole_0))
% 0.49/0.70          | ((X11) = (k1_xboole_0))
% 0.49/0.70          | ~ (v1_relat_1 @ X11))),
% 0.49/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.49/0.70  thf('35', plain,
% 0.49/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.70        | ~ (v1_relat_1 @ sk_A)
% 0.49/0.70        | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.70  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('37', plain,
% 0.49/0.70      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.70      inference('demod', [status(thm)], ['35', '36'])).
% 0.49/0.70  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.70  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.70  thf(t71_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.49/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.49/0.70  thf('40', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.49/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.70  thf('41', plain,
% 0.49/0.70      (![X11 : $i]:
% 0.49/0.70         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 0.49/0.70          | ((X11) = (k1_xboole_0))
% 0.49/0.70          | ~ (v1_relat_1 @ X11))),
% 0.49/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.49/0.70  thf('42', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((X0) != (k1_xboole_0))
% 0.49/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.49/0.70          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.70  thf(fc3_funct_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.49/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.49/0.70  thf('43', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.49/0.70  thf('44', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.49/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.70  thf('45', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['44'])).
% 0.49/0.70  thf('46', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.49/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.49/0.70  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.70      inference('sup+', [status(thm)], ['45', '46'])).
% 0.49/0.70  thf(t4_subset_1, axiom,
% 0.49/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.70  thf('48', plain,
% 0.49/0.70      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.70  thf('49', plain,
% 0.49/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.70         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.49/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.70  thf('50', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.70  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.70      inference('sup+', [status(thm)], ['45', '46'])).
% 0.49/0.70  thf('52', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['50', '51'])).
% 0.49/0.70  thf('53', plain,
% 0.49/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.70         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 0.49/0.70          | (v1_funct_2 @ X23 @ X21 @ X22)
% 0.49/0.70          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.70  thf('54', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (((X1) != (k1_xboole_0))
% 0.49/0.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.49/0.70          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['52', '53'])).
% 0.49/0.70  thf('55', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.49/0.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['54'])).
% 0.49/0.70  thf('56', plain,
% 0.49/0.70      (![X19 : $i, X20 : $i]:
% 0.49/0.70         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.70  thf('57', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 0.49/0.70      inference('simplify', [status(thm)], ['56'])).
% 0.49/0.70  thf('58', plain,
% 0.49/0.70      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.70  thf('59', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.49/0.70         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.49/0.70          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.49/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.70  thf('60', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.49/0.70  thf('61', plain,
% 0.49/0.70      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.49/0.70      inference('sup-', [status(thm)], ['57', '60'])).
% 0.49/0.70  thf('62', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.49/0.70      inference('demod', [status(thm)], ['55', '61'])).
% 0.49/0.70  thf('63', plain, ($false),
% 0.49/0.70      inference('demod', [status(thm)], ['32', '38', '39', '47', '62'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
