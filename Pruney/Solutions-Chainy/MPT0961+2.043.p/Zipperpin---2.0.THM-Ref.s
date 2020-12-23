%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxjCZqPQwC

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:44 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 465 expanded)
%              Number of leaves         :   32 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  782 (5136 expanded)
%              Number of equality atoms :   55 ( 178 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X14: $i] :
      ( ( r1_tarski @ X14 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
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
    ! [X14: $i] :
      ( ( r1_tarski @ X14 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('46',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('47',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('48',plain,(
    ! [X14: $i] :
      ( ( r1_tarski @ X14 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('60',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['57','58'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('71',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['67','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['32','44','45','59','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxjCZqPQwC
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 215 iterations in 0.170s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.63  thf(t3_funct_2, conjecture,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.63       ( ( v1_funct_1 @ A ) & 
% 0.37/0.63         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.37/0.63         ( m1_subset_1 @
% 0.37/0.63           A @ 
% 0.37/0.63           ( k1_zfmisc_1 @
% 0.37/0.63             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i]:
% 0.37/0.63        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.63          ( ( v1_funct_1 @ A ) & 
% 0.37/0.63            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.37/0.63            ( m1_subset_1 @
% 0.37/0.63              A @ 
% 0.37/0.63              ( k1_zfmisc_1 @
% 0.37/0.63                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.37/0.63  thf('0', plain,
% 0.37/0.63      ((~ (v1_funct_1 @ sk_A)
% 0.37/0.63        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.37/0.63        | ~ (m1_subset_1 @ sk_A @ 
% 0.37/0.63             (k1_zfmisc_1 @ 
% 0.37/0.63              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('1', plain,
% 0.37/0.63      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.37/0.63         <= (~
% 0.37/0.63             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.63  thf(t21_relat_1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v1_relat_1 @ A ) =>
% 0.37/0.63       ( r1_tarski @
% 0.37/0.63         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      (![X14 : $i]:
% 0.37/0.63         ((r1_tarski @ X14 @ 
% 0.37/0.63           (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 0.37/0.63          | ~ (v1_relat_1 @ X14))),
% 0.37/0.63      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.37/0.63  thf(t3_subset, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.63  thf('6', plain,
% 0.37/0.63      (![X8 : $i, X10 : $i]:
% 0.37/0.63         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.37/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.63  thf('7', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (v1_relat_1 @ X0)
% 0.37/0.63          | (m1_subset_1 @ X0 @ 
% 0.37/0.63             (k1_zfmisc_1 @ 
% 0.37/0.63              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.63  thf('8', plain,
% 0.37/0.63      ((~ (m1_subset_1 @ sk_A @ 
% 0.37/0.63           (k1_zfmisc_1 @ 
% 0.37/0.63            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.37/0.63         <= (~
% 0.37/0.63             ((m1_subset_1 @ sk_A @ 
% 0.37/0.63               (k1_zfmisc_1 @ 
% 0.37/0.63                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('9', plain,
% 0.37/0.63      ((~ (v1_relat_1 @ sk_A))
% 0.37/0.63         <= (~
% 0.37/0.63             ((m1_subset_1 @ sk_A @ 
% 0.37/0.63               (k1_zfmisc_1 @ 
% 0.37/0.63                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.63  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (((m1_subset_1 @ sk_A @ 
% 0.37/0.63         (k1_zfmisc_1 @ 
% 0.37/0.63          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.63  thf('12', plain,
% 0.37/0.63      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.37/0.63       ~
% 0.37/0.63       ((m1_subset_1 @ sk_A @ 
% 0.37/0.63         (k1_zfmisc_1 @ 
% 0.37/0.63          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.37/0.63       ~ ((v1_funct_1 @ sk_A))),
% 0.37/0.63      inference('split', [status(esa)], ['0'])).
% 0.37/0.63  thf('13', plain,
% 0.37/0.63      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.37/0.63      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.37/0.63      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.46/0.63  thf(d1_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_1, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | (m1_subset_1 @ X0 @ 
% 0.46/0.63             (k1_zfmisc_1 @ 
% 0.46/0.63              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_3, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_5, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.63         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.46/0.63          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.46/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.63          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['15', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | (m1_subset_1 @ X0 @ 
% 0.46/0.63             (k1_zfmisc_1 @ 
% 0.46/0.63              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.63         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.46/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.46/0.63              = (k1_relat_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.63         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 0.46/0.63          | (v1_funct_2 @ X26 @ X24 @ X25)
% 0.46/0.63          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.63          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.63          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['19', '25'])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.63          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.46/0.63      inference('demod', [status(thm)], ['14', '31'])).
% 0.46/0.63  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X14 : $i]:
% 0.46/0.63         ((r1_tarski @ X14 @ 
% 0.46/0.63           (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 0.46/0.63          | ~ (v1_relat_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.46/0.63  thf(d10_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X0 : $i, X2 : $i]:
% 0.46/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (r1_tarski @ 
% 0.46/0.63               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.46/0.63          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0) @ sk_A)
% 0.46/0.63        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) = (sk_A))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['33', '36'])).
% 0.46/0.63  thf(t113_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i]:
% 0.46/0.63         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.63  thf('40', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.63  thf('41', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.63  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('44', plain, (((k1_xboole_0) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.46/0.63  thf('45', plain, (((k1_xboole_0) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.63  thf(t71_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.63       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.63  thf('47', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.46/0.63      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (![X14 : $i]:
% 0.46/0.63         ((r1_tarski @ X14 @ 
% 0.46/0.63           (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 0.46/0.63          | ~ (v1_relat_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r1_tarski @ (k6_relat_1 @ X0) @ 
% 0.46/0.63           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.46/0.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.63  thf('50', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.63  thf(fc4_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.63       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.63  thf('51', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.46/0.63  thf('53', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.46/0.63      inference('sup+', [status(thm)], ['46', '52'])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (![X0 : $i, X2 : $i]:
% 0.46/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      ((~ (r1_tarski @ k1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))
% 0.46/0.63        | ((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.63  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.63  thf('57', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.63  thf('58', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.46/0.63      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.63  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.63  thf(t4_subset_1, axiom,
% 0.46/0.63    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.63         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.46/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.63  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.63         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 0.46/0.63          | (v1_funct_2 @ X26 @ X24 @ X25)
% 0.46/0.63          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((X1) != (k1_xboole_0))
% 0.46/0.63          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.46/0.63          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.63          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.63  thf('69', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.46/0.63      inference('simplify', [status(thm)], ['68'])).
% 0.46/0.63  thf('70', plain,
% 0.46/0.63      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.63  thf('71', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.63         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.46/0.63          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.46/0.63          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.63      inference('sup-', [status(thm)], ['69', '72'])).
% 0.46/0.63  thf('74', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.63      inference('demod', [status(thm)], ['67', '73'])).
% 0.46/0.63  thf('75', plain, ($false),
% 0.46/0.63      inference('demod', [status(thm)], ['32', '44', '45', '59', '74'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
