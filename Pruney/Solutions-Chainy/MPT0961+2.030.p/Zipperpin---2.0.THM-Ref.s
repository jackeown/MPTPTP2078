%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lRJDQgFDIn

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:42 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  166 (3164 expanded)
%              Number of leaves         :   29 ( 891 expanded)
%              Depth                    :   26
%              Number of atoms          : 1267 (35495 expanded)
%              Number of equality atoms :   80 ( 766 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X7: $i] :
      ( ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['36','37'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','40','41','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','40','41','42'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ( X24 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','62'])).

thf('64',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_funct_2 @ X0 @ X1 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( X1 = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','64'])).

thf('66',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ X2 @ X1 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( X1 = k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X2 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','65'])).

thf('67',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('68',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ( ( k1_relat_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('78',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('79',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['76','81'])).

thf('83',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 )
        | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('99',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['68','99'])).

thf('101',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['36','37'])).

thf('102',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('105',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','54'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','54'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('112',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('114',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('115',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('117',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('126',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('127',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('131',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['124','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['109','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lRJDQgFDIn
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:47:57 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.52/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.77  % Solved by: fo/fo7.sh
% 0.52/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.77  % done 342 iterations in 0.287s
% 0.52/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.77  % SZS output start Refutation
% 0.52/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.77  thf(t3_funct_2, conjecture,
% 0.52/0.77    (![A:$i]:
% 0.52/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.77       ( ( v1_funct_1 @ A ) & 
% 0.52/0.77         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.52/0.77         ( m1_subset_1 @
% 0.52/0.77           A @ 
% 0.52/0.77           ( k1_zfmisc_1 @
% 0.52/0.77             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.77    (~( ![A:$i]:
% 0.52/0.77        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.77          ( ( v1_funct_1 @ A ) & 
% 0.52/0.77            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.52/0.77            ( m1_subset_1 @
% 0.52/0.77              A @ 
% 0.52/0.77              ( k1_zfmisc_1 @
% 0.52/0.77                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.52/0.77    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.52/0.77  thf('0', plain,
% 0.52/0.77      ((~ (v1_funct_1 @ sk_A)
% 0.52/0.77        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.52/0.77        | ~ (m1_subset_1 @ sk_A @ 
% 0.52/0.77             (k1_zfmisc_1 @ 
% 0.52/0.77              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('1', plain,
% 0.52/0.77      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.52/0.77         <= (~
% 0.52/0.77             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.52/0.77      inference('split', [status(esa)], ['0'])).
% 0.52/0.77  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.52/0.77      inference('split', [status(esa)], ['0'])).
% 0.52/0.77  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.52/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.77  thf(t21_relat_1, axiom,
% 0.52/0.77    (![A:$i]:
% 0.52/0.77     ( ( v1_relat_1 @ A ) =>
% 0.52/0.77       ( r1_tarski @
% 0.52/0.77         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.52/0.77  thf('5', plain,
% 0.52/0.77      (![X7 : $i]:
% 0.52/0.77         ((r1_tarski @ X7 @ 
% 0.52/0.77           (k2_zfmisc_1 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.52/0.77          | ~ (v1_relat_1 @ X7))),
% 0.52/0.77      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.52/0.77  thf(t3_subset, axiom,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.77  thf('6', plain,
% 0.52/0.77      (![X4 : $i, X6 : $i]:
% 0.52/0.77         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.52/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.77  thf('7', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (m1_subset_1 @ X0 @ 
% 0.52/0.77             (k1_zfmisc_1 @ 
% 0.52/0.77              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.77  thf('8', plain,
% 0.52/0.77      ((~ (m1_subset_1 @ sk_A @ 
% 0.52/0.77           (k1_zfmisc_1 @ 
% 0.52/0.77            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.52/0.77         <= (~
% 0.52/0.77             ((m1_subset_1 @ sk_A @ 
% 0.52/0.77               (k1_zfmisc_1 @ 
% 0.52/0.77                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.52/0.77      inference('split', [status(esa)], ['0'])).
% 0.52/0.77  thf('9', plain,
% 0.52/0.77      ((~ (v1_relat_1 @ sk_A))
% 0.52/0.77         <= (~
% 0.52/0.77             ((m1_subset_1 @ sk_A @ 
% 0.52/0.77               (k1_zfmisc_1 @ 
% 0.52/0.77                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.77  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('11', plain,
% 0.52/0.77      (((m1_subset_1 @ sk_A @ 
% 0.52/0.77         (k1_zfmisc_1 @ 
% 0.52/0.77          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.52/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.77  thf('12', plain,
% 0.52/0.77      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.52/0.77       ~
% 0.52/0.77       ((m1_subset_1 @ sk_A @ 
% 0.52/0.77         (k1_zfmisc_1 @ 
% 0.52/0.77          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.52/0.77       ~ ((v1_funct_1 @ sk_A))),
% 0.52/0.77      inference('split', [status(esa)], ['0'])).
% 0.52/0.77  thf('13', plain,
% 0.52/0.77      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.52/0.77      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.52/0.77  thf('14', plain,
% 0.52/0.77      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.52/0.77      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.52/0.77  thf(d1_funct_2, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i]:
% 0.52/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.77  thf(zf_stmt_1, axiom,
% 0.52/0.77    (![B:$i,A:$i]:
% 0.52/0.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.77       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.77  thf('15', plain,
% 0.52/0.77      (![X17 : $i, X18 : $i]:
% 0.52/0.77         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.77  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.77  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.77  thf('17', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.52/0.77      inference('sup+', [status(thm)], ['15', '16'])).
% 0.52/0.77  thf('18', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (m1_subset_1 @ X0 @ 
% 0.52/0.77             (k1_zfmisc_1 @ 
% 0.52/0.77              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.77  thf(cc4_relset_1, axiom,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( v1_xboole_0 @ A ) =>
% 0.52/0.77       ( ![C:$i]:
% 0.52/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.52/0.77           ( v1_xboole_0 @ C ) ) ) ))).
% 0.52/0.77  thf('19', plain,
% 0.52/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.77         (~ (v1_xboole_0 @ X8)
% 0.52/0.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 0.52/0.77          | (v1_xboole_0 @ X9))),
% 0.52/0.77      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.52/0.77  thf('20', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (v1_xboole_0 @ X0)
% 0.52/0.77          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.77  thf('21', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i]:
% 0.52/0.77         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 0.52/0.77          | (v1_xboole_0 @ X0)
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['17', '20'])).
% 0.52/0.77  thf('22', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (m1_subset_1 @ X0 @ 
% 0.52/0.77             (k1_zfmisc_1 @ 
% 0.52/0.77              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.77  thf(zf_stmt_3, axiom,
% 0.52/0.77    (![C:$i,B:$i,A:$i]:
% 0.52/0.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.77  thf(zf_stmt_5, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i]:
% 0.52/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.77  thf('23', plain,
% 0.52/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.77         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.52/0.77          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.52/0.77          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.77  thf('24', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.77  thf('25', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (v1_xboole_0 @ X0)
% 0.52/0.77          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['21', '24'])).
% 0.52/0.77  thf('26', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | (v1_xboole_0 @ X0)
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['25'])).
% 0.52/0.77  thf('27', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (m1_subset_1 @ X0 @ 
% 0.52/0.77             (k1_zfmisc_1 @ 
% 0.52/0.77              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.77  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i]:
% 0.52/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.77  thf('28', plain,
% 0.52/0.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.77         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.52/0.77          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.52/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.77  thf('29', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.52/0.77              = (k1_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.77  thf('30', plain,
% 0.52/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.77         (((X19) != (k1_relset_1 @ X19 @ X20 @ X21))
% 0.52/0.77          | (v1_funct_2 @ X21 @ X19 @ X20)
% 0.52/0.77          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.77  thf('31', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0)
% 0.52/0.77          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.77  thf('32', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.77          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['31'])).
% 0.52/0.77  thf('33', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (v1_xboole_0 @ X0)
% 0.52/0.77          | ~ (v1_relat_1 @ X0)
% 0.52/0.77          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['26', '32'])).
% 0.52/0.77  thf('34', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.77          | (v1_xboole_0 @ X0)
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['33'])).
% 0.52/0.77  thf('35', plain,
% 0.52/0.77      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.52/0.77      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.52/0.77  thf('36', plain, ((~ (v1_relat_1 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.52/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.77  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('38', plain, ((v1_xboole_0 @ sk_A)),
% 0.52/0.77      inference('demod', [status(thm)], ['36', '37'])).
% 0.52/0.77  thf(l13_xboole_0, axiom,
% 0.52/0.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.77  thf('39', plain,
% 0.52/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.77  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.77  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.77  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.77  thf('43', plain,
% 0.52/0.77      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.52/0.77          (k2_relat_1 @ k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['14', '40', '41', '42'])).
% 0.52/0.77  thf('44', plain,
% 0.52/0.77      (![X17 : $i, X18 : $i]:
% 0.52/0.77         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.77  thf('45', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.77  thf('46', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.52/0.77          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.77  thf('47', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.77          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['31'])).
% 0.52/0.77  thf('48', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0)
% 0.52/0.77          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.77  thf('49', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.77          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['48'])).
% 0.52/0.77  thf('50', plain,
% 0.52/0.77      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.52/0.77          (k2_relat_1 @ k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['14', '40', '41', '42'])).
% 0.52/0.77  thf('51', plain,
% 0.52/0.77      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.77        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['49', '50'])).
% 0.52/0.77  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.77  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.77      inference('demod', [status(thm)], ['52', '53'])).
% 0.52/0.77  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['51', '54'])).
% 0.52/0.77  thf('56', plain,
% 0.52/0.77      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.52/0.77      inference('demod', [status(thm)], ['43', '55'])).
% 0.52/0.77  thf('57', plain,
% 0.52/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.77  thf('58', plain,
% 0.52/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.77  thf('59', plain,
% 0.52/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.77         (((X22) != (k1_xboole_0))
% 0.52/0.77          | ((X23) = (k1_xboole_0))
% 0.52/0.77          | (v1_funct_2 @ X24 @ X23 @ X22)
% 0.52/0.77          | ((X24) != (k1_xboole_0))
% 0.52/0.77          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.77  thf('60', plain,
% 0.52/0.77      (![X23 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.52/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ k1_xboole_0)))
% 0.52/0.77          | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)
% 0.52/0.77          | ((X23) = (k1_xboole_0)))),
% 0.52/0.77      inference('simplify', [status(thm)], ['59'])).
% 0.52/0.77  thf(t113_zfmisc_1, axiom,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.77  thf('61', plain,
% 0.52/0.77      (![X2 : $i, X3 : $i]:
% 0.52/0.77         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.52/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.77  thf('62', plain,
% 0.52/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['61'])).
% 0.52/0.77  thf('63', plain,
% 0.52/0.77      (![X23 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.77          | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)
% 0.52/0.77          | ((X23) = (k1_xboole_0)))),
% 0.52/0.77      inference('demod', [status(thm)], ['60', '62'])).
% 0.52/0.77  thf('64', plain,
% 0.52/0.77      ((![X23 : $i]:
% 0.52/0.77          (((X23) = (k1_xboole_0))
% 0.52/0.77           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))
% 0.52/0.77         <= ((![X23 : $i]:
% 0.52/0.77                (((X23) = (k1_xboole_0))
% 0.52/0.77                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.52/0.77      inference('split', [status(esa)], ['63'])).
% 0.52/0.77  thf('65', plain,
% 0.52/0.77      ((![X0 : $i, X1 : $i]:
% 0.52/0.77          ((v1_funct_2 @ X0 @ X1 @ k1_xboole_0)
% 0.52/0.77           | ~ (v1_xboole_0 @ X0)
% 0.52/0.77           | ((X1) = (k1_xboole_0))))
% 0.52/0.77         <= ((![X23 : $i]:
% 0.52/0.77                (((X23) = (k1_xboole_0))
% 0.52/0.77                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup+', [status(thm)], ['58', '64'])).
% 0.52/0.77  thf('66', plain,
% 0.52/0.77      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77          ((v1_funct_2 @ X2 @ X1 @ X0)
% 0.52/0.77           | ~ (v1_xboole_0 @ X0)
% 0.52/0.77           | ((X1) = (k1_xboole_0))
% 0.52/0.77           | ~ (v1_xboole_0 @ X2)))
% 0.52/0.77         <= ((![X23 : $i]:
% 0.52/0.77                (((X23) = (k1_xboole_0))
% 0.52/0.77                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup+', [status(thm)], ['57', '65'])).
% 0.52/0.77  thf('67', plain,
% 0.52/0.77      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.52/0.77      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.52/0.77  thf('68', plain,
% 0.52/0.77      (((~ (v1_xboole_0 @ sk_A)
% 0.52/0.77         | ((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.52/0.77         | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_A))))
% 0.52/0.77         <= ((![X23 : $i]:
% 0.52/0.77                (((X23) = (k1_xboole_0))
% 0.52/0.77                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.77  thf('69', plain,
% 0.52/0.77      (![X17 : $i, X18 : $i]:
% 0.52/0.77         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.77  thf('70', plain,
% 0.52/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['61'])).
% 0.52/0.77  thf('71', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.52/0.77      inference('sup+', [status(thm)], ['69', '70'])).
% 0.52/0.77  thf('72', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (m1_subset_1 @ X0 @ 
% 0.52/0.77             (k1_zfmisc_1 @ 
% 0.52/0.77              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.77  thf('73', plain,
% 0.52/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.77  thf('74', plain,
% 0.52/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.77  thf('75', plain,
% 0.52/0.77      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('split', [status(esa)], ['63'])).
% 0.52/0.77  thf('76', plain,
% 0.52/0.77      ((![X0 : $i]:
% 0.52/0.77          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.77           | ~ (v1_xboole_0 @ X0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.52/0.77  thf('77', plain,
% 0.52/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['61'])).
% 0.52/0.77  thf('78', plain,
% 0.52/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.77         (~ (v1_xboole_0 @ X8)
% 0.52/0.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 0.52/0.77          | (v1_xboole_0 @ X9))),
% 0.52/0.77      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.52/0.77  thf('79', plain,
% 0.52/0.77      (![X1 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.77          | (v1_xboole_0 @ X1)
% 0.52/0.77          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['77', '78'])).
% 0.52/0.77  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.77  thf('81', plain,
% 0.52/0.77      (![X1 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.77          | (v1_xboole_0 @ X1))),
% 0.52/0.77      inference('demod', [status(thm)], ['79', '80'])).
% 0.52/0.77  thf('82', plain,
% 0.52/0.77      ((![X0 : $i]: ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('clc', [status(thm)], ['76', '81'])).
% 0.52/0.77  thf('83', plain,
% 0.52/0.77      ((![X0 : $i, X1 : $i]:
% 0.52/0.77          (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['73', '82'])).
% 0.52/0.77  thf('84', plain,
% 0.52/0.77      ((![X0 : $i]:
% 0.52/0.77          (~ (v1_relat_1 @ X0)
% 0.52/0.77           | ~ (v1_xboole_0 @ 
% 0.52/0.77                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['72', '83'])).
% 0.52/0.77  thf('85', plain,
% 0.52/0.77      ((![X0 : $i, X1 : $i]:
% 0.52/0.77          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.77           | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 0.52/0.77           | ~ (v1_relat_1 @ X0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['71', '84'])).
% 0.52/0.77  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.77  thf('87', plain,
% 0.52/0.77      ((![X0 : $i, X1 : $i]:
% 0.52/0.77          ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1) | ~ (v1_relat_1 @ X0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('demod', [status(thm)], ['85', '86'])).
% 0.52/0.77  thf('88', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.77  thf('89', plain,
% 0.52/0.77      ((![X0 : $i]:
% 0.52/0.77          (~ (v1_relat_1 @ X0)
% 0.52/0.77           | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77           | ~ (v1_relat_1 @ X0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['87', '88'])).
% 0.52/0.77  thf('90', plain,
% 0.52/0.77      ((![X0 : $i]:
% 0.52/0.77          ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77           | ~ (v1_relat_1 @ X0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('simplify', [status(thm)], ['89'])).
% 0.52/0.77  thf('91', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.77          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.52/0.77          | ~ (v1_relat_1 @ X0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['31'])).
% 0.52/0.77  thf('92', plain,
% 0.52/0.77      ((![X0 : $i]:
% 0.52/0.77          (~ (v1_relat_1 @ X0)
% 0.52/0.77           | ~ (v1_relat_1 @ X0)
% 0.52/0.77           | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['90', '91'])).
% 0.52/0.77  thf('93', plain,
% 0.52/0.77      ((![X0 : $i]:
% 0.52/0.77          ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.77           | ~ (v1_relat_1 @ X0)))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('simplify', [status(thm)], ['92'])).
% 0.52/0.77  thf('94', plain,
% 0.52/0.77      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.52/0.77      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.52/0.77  thf('95', plain,
% 0.52/0.77      ((~ (v1_relat_1 @ sk_A))
% 0.52/0.77         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['93', '94'])).
% 0.52/0.77  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('97', plain,
% 0.52/0.77      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.52/0.77      inference('demod', [status(thm)], ['95', '96'])).
% 0.52/0.77  thf('98', plain,
% 0.52/0.77      ((![X23 : $i]:
% 0.52/0.77          (((X23) = (k1_xboole_0))
% 0.52/0.77           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))) | 
% 0.52/0.77       ~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.52/0.77      inference('split', [status(esa)], ['63'])).
% 0.52/0.77  thf('99', plain,
% 0.52/0.77      ((![X23 : $i]:
% 0.52/0.77          (((X23) = (k1_xboole_0))
% 0.52/0.77           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))),
% 0.52/0.77      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 0.52/0.77  thf('100', plain,
% 0.52/0.77      ((~ (v1_xboole_0 @ sk_A)
% 0.52/0.77        | ((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.52/0.77        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_A)))),
% 0.52/0.77      inference('simpl_trail', [status(thm)], ['68', '99'])).
% 0.52/0.77  thf('101', plain, ((v1_xboole_0 @ sk_A)),
% 0.52/0.77      inference('demod', [status(thm)], ['36', '37'])).
% 0.52/0.77  thf('102', plain,
% 0.52/0.77      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.52/0.77        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_A)))),
% 0.52/0.77      inference('demod', [status(thm)], ['100', '101'])).
% 0.52/0.77  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.77  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.77  thf('105', plain,
% 0.52/0.77      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.77        | ~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.52/0.77      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.52/0.77  thf('106', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['51', '54'])).
% 0.52/0.77  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.77  thf('108', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.52/0.77  thf('109', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.52/0.77      inference('demod', [status(thm)], ['56', '108'])).
% 0.52/0.77  thf('110', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['51', '54'])).
% 0.52/0.77  thf('111', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (~ (v1_relat_1 @ X0)
% 0.52/0.77          | (m1_subset_1 @ X0 @ 
% 0.52/0.77             (k1_zfmisc_1 @ 
% 0.52/0.77              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.52/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.77  thf('112', plain,
% 0.52/0.77      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.52/0.77         (k1_zfmisc_1 @ 
% 0.52/0.77          (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))
% 0.52/0.77        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.52/0.77      inference('sup+', [status(thm)], ['110', '111'])).
% 0.52/0.77  thf('113', plain,
% 0.52/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['61'])).
% 0.52/0.77  thf('114', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.77      inference('demod', [status(thm)], ['52', '53'])).
% 0.52/0.77  thf('115', plain,
% 0.52/0.77      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.52/0.77  thf('116', plain,
% 0.52/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['61'])).
% 0.52/0.77  thf('117', plain,
% 0.52/0.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.77         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.52/0.77          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.52/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.77  thf('118', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.77          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_relat_1 @ X1)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['116', '117'])).
% 0.52/0.77  thf('119', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.52/0.77           = (k1_relat_1 @ k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['115', '118'])).
% 0.52/0.77  thf('120', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.52/0.77  thf('121', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['119', '120'])).
% 0.52/0.77  thf('122', plain,
% 0.52/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.77         (((X19) != (k1_relset_1 @ X19 @ X20 @ X21))
% 0.52/0.77          | (v1_funct_2 @ X21 @ X19 @ X20)
% 0.52/0.77          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.77  thf('123', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (((X0) != (k1_xboole_0))
% 0.52/0.77          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.77          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['121', '122'])).
% 0.52/0.77  thf('124', plain,
% 0.52/0.77      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.52/0.77        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['123'])).
% 0.52/0.77  thf('125', plain,
% 0.52/0.77      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.52/0.77  thf('126', plain,
% 0.52/0.77      (![X2 : $i, X3 : $i]:
% 0.52/0.77         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.52/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.77  thf('127', plain,
% 0.52/0.77      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.52/0.77      inference('simplify', [status(thm)], ['126'])).
% 0.52/0.77  thf('128', plain,
% 0.52/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.77         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.52/0.77          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.52/0.77          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.77  thf('129', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.77          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.52/0.77          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.52/0.77      inference('sup-', [status(thm)], ['127', '128'])).
% 0.52/0.77  thf('130', plain,
% 0.52/0.77      (![X17 : $i, X18 : $i]:
% 0.52/0.77         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.77  thf('131', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 0.52/0.77      inference('simplify', [status(thm)], ['130'])).
% 0.52/0.77  thf('132', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.77          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.52/0.77      inference('demod', [status(thm)], ['129', '131'])).
% 0.52/0.77  thf('133', plain,
% 0.52/0.77      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.52/0.77      inference('sup-', [status(thm)], ['125', '132'])).
% 0.52/0.77  thf('134', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.52/0.77      inference('simplify_reflect+', [status(thm)], ['124', '133'])).
% 0.52/0.77  thf('135', plain, ($false), inference('demod', [status(thm)], ['109', '134'])).
% 0.52/0.77  
% 0.52/0.77  % SZS output end Refutation
% 0.52/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
