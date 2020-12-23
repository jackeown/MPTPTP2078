%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uqtgApMjZB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 477 expanded)
%              Number of leaves         :   32 ( 150 expanded)
%              Depth                    :   12
%              Number of atoms          :  791 (5158 expanded)
%              Number of equality atoms :   48 ( 146 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf('46',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('62',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','59'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('72',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['68','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['32','44','45','60','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uqtgApMjZB
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 347 iterations in 0.204s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.65  thf(t3_funct_2, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v1_funct_1 @ A ) & 
% 0.45/0.65         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.65         ( m1_subset_1 @
% 0.45/0.65           A @ 
% 0.45/0.65           ( k1_zfmisc_1 @
% 0.45/0.65             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65          ( ( v1_funct_1 @ A ) & 
% 0.45/0.65            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.65            ( m1_subset_1 @
% 0.45/0.65              A @ 
% 0.45/0.65              ( k1_zfmisc_1 @
% 0.45/0.65                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_A)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.45/0.65        | ~ (m1_subset_1 @ sk_A @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.45/0.65         <= (~
% 0.45/0.65             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(t21_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( r1_tarski @
% 0.45/0.65         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X12 : $i]:
% 0.45/0.65         ((r1_tarski @ X12 @ 
% 0.45/0.65           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.45/0.65          | ~ (v1_relat_1 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.45/0.65  thf(t3_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X7 : $i, X9 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ sk_A @ 
% 0.45/0.65           (k1_zfmisc_1 @ 
% 0.45/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ sk_A @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_A))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ sk_A @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (((m1_subset_1 @ sk_A @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.45/0.65       ~
% 0.45/0.65       ((m1_subset_1 @ sk_A @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.45/0.65       ~ ((v1_funct_1 @ sk_A))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.45/0.65  thf(d1_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_1, axiom,
% 0.45/0.65    (![B:$i,A:$i]:
% 0.45/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X22 : $i, X23 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_3, axiom,
% 0.45/0.65    (![C:$i,B:$i,A:$i]:
% 0.45/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_5, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.65         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.45/0.65          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.45/0.65          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.65         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.45/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.45/0.65              = (k1_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.65         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 0.45/0.65          | (v1_funct_2 @ X26 @ X24 @ X25)
% 0.45/0.65          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['19', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['14', '31'])).
% 0.45/0.65  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X12 : $i]:
% 0.45/0.65         ((r1_tarski @ X12 @ 
% 0.45/0.65           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.45/0.65          | ~ (v1_relat_1 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i, X2 : $i]:
% 0.45/0.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (r1_tarski @ 
% 0.45/0.65               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.45/0.65          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0) @ sk_A)
% 0.45/0.65        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) = (sk_A))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['33', '36'])).
% 0.45/0.65  thf(t113_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i]:
% 0.45/0.65         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.65  thf('40', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.65  thf('41', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.65  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('44', plain, (((k1_xboole_0) = (sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.45/0.65  thf('45', plain, (((k1_xboole_0) = (sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['37', '39', '40', '41', '42', '43'])).
% 0.45/0.65  thf('46', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X7 : $i, X9 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf(cc2_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.65         ((v4_relat_1 @ X16 @ X17)
% 0.45/0.65          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.65  thf('50', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.65  thf(d18_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ B ) =>
% 0.45/0.65       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         (~ (v4_relat_1 @ X10 @ X11)
% 0.45/0.65          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.45/0.65          | ~ (v1_relat_1 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.65          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf(cc1_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( v1_relat_1 @ C ) ))).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.65         ((v1_relat_1 @ X13)
% 0.45/0.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.65  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.65  thf('56', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.45/0.65      inference('demod', [status(thm)], ['52', '55'])).
% 0.45/0.65  thf('57', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X0 : $i, X2 : $i]:
% 0.45/0.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.65  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['56', '59'])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.65         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.45/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.65  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['56', '59'])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['63', '64'])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.65         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 0.45/0.65          | (v1_funct_2 @ X26 @ X24 @ X25)
% 0.45/0.65          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X1) != (k1_xboole_0))
% 0.45/0.65          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.45/0.65          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.65          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (![X22 : $i, X23 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.65  thf('70', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['69'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.65         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.45/0.65          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.45/0.65          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['70', '73'])).
% 0.45/0.65  thf('75', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.65      inference('demod', [status(thm)], ['68', '74'])).
% 0.45/0.65  thf('76', plain, ($false),
% 0.45/0.65      inference('demod', [status(thm)], ['32', '44', '45', '60', '75'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
