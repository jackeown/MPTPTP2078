%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AWmaxlmhTw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:41 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  168 (3598 expanded)
%              Number of leaves         :   29 (1015 expanded)
%              Depth                    :   26
%              Number of atoms          : 1286 (38595 expanded)
%              Number of equality atoms :   81 (1231 expanded)
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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('24',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('53',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','50','51','52'])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','50','51','52'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('64',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ( X24 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('72',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_funct_2 @ X0 @ X1 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( X1 = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ X2 @ X1 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( X1 = k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X2 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('77',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ( ( k1_relat_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['72'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('85',plain,
    ( ! [X0: $i] :
        ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 )
        | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['72'])).

thf('102',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['77','102'])).

thf('104',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('105',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('108',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','64'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','64'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('115',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('117',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('118',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('120',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('129',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('130',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('133',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['131','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['127','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['112','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AWmaxlmhTw
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.56/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.79  % Solved by: fo/fo7.sh
% 0.56/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.79  % done 342 iterations in 0.325s
% 0.56/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.79  % SZS output start Refutation
% 0.56/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.56/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.56/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.56/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.79  thf(t3_funct_2, conjecture,
% 0.56/0.79    (![A:$i]:
% 0.56/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.56/0.79       ( ( v1_funct_1 @ A ) & 
% 0.56/0.79         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.56/0.79         ( m1_subset_1 @
% 0.56/0.79           A @ 
% 0.56/0.79           ( k1_zfmisc_1 @
% 0.56/0.79             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.56/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.79    (~( ![A:$i]:
% 0.56/0.79        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.56/0.79          ( ( v1_funct_1 @ A ) & 
% 0.56/0.79            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.56/0.79            ( m1_subset_1 @
% 0.56/0.79              A @ 
% 0.56/0.79              ( k1_zfmisc_1 @
% 0.56/0.79                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.56/0.79    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.56/0.79  thf('0', plain,
% 0.56/0.79      ((~ (v1_funct_1 @ sk_A)
% 0.56/0.79        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.56/0.79        | ~ (m1_subset_1 @ sk_A @ 
% 0.56/0.79             (k1_zfmisc_1 @ 
% 0.56/0.79              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.79  thf('1', plain,
% 0.56/0.79      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.56/0.79         <= (~
% 0.56/0.79             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.56/0.79      inference('split', [status(esa)], ['0'])).
% 0.56/0.79  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.79  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.56/0.79      inference('split', [status(esa)], ['0'])).
% 0.56/0.79  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.56/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.79  thf(t21_relat_1, axiom,
% 0.56/0.79    (![A:$i]:
% 0.56/0.79     ( ( v1_relat_1 @ A ) =>
% 0.56/0.79       ( r1_tarski @
% 0.56/0.79         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.56/0.79  thf('5', plain,
% 0.56/0.79      (![X7 : $i]:
% 0.56/0.79         ((r1_tarski @ X7 @ 
% 0.56/0.79           (k2_zfmisc_1 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.56/0.79          | ~ (v1_relat_1 @ X7))),
% 0.56/0.79      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.56/0.79  thf(t3_subset, axiom,
% 0.56/0.79    (![A:$i,B:$i]:
% 0.56/0.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.79  thf('6', plain,
% 0.56/0.79      (![X4 : $i, X6 : $i]:
% 0.56/0.79         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.56/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.79  thf('7', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (m1_subset_1 @ X0 @ 
% 0.56/0.79             (k1_zfmisc_1 @ 
% 0.56/0.79              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.79  thf('8', plain,
% 0.56/0.79      ((~ (m1_subset_1 @ sk_A @ 
% 0.56/0.79           (k1_zfmisc_1 @ 
% 0.56/0.79            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.56/0.79         <= (~
% 0.56/0.79             ((m1_subset_1 @ sk_A @ 
% 0.56/0.79               (k1_zfmisc_1 @ 
% 0.56/0.79                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.56/0.79      inference('split', [status(esa)], ['0'])).
% 0.56/0.79  thf('9', plain,
% 0.56/0.79      ((~ (v1_relat_1 @ sk_A))
% 0.56/0.79         <= (~
% 0.56/0.79             ((m1_subset_1 @ sk_A @ 
% 0.56/0.79               (k1_zfmisc_1 @ 
% 0.56/0.79                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.56/0.79  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.79  thf('11', plain,
% 0.56/0.79      (((m1_subset_1 @ sk_A @ 
% 0.56/0.79         (k1_zfmisc_1 @ 
% 0.56/0.79          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.56/0.79      inference('demod', [status(thm)], ['9', '10'])).
% 0.56/0.79  thf('12', plain,
% 0.56/0.79      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.56/0.79       ~
% 0.56/0.79       ((m1_subset_1 @ sk_A @ 
% 0.56/0.79         (k1_zfmisc_1 @ 
% 0.56/0.79          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.56/0.79       ~ ((v1_funct_1 @ sk_A))),
% 0.56/0.79      inference('split', [status(esa)], ['0'])).
% 0.56/0.79  thf('13', plain,
% 0.56/0.79      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.56/0.79      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.56/0.79  thf('14', plain,
% 0.56/0.79      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.56/0.79      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.56/0.79  thf(d1_funct_2, axiom,
% 0.56/0.79    (![A:$i,B:$i,C:$i]:
% 0.56/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.56/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.56/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.56/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.56/0.79  thf(zf_stmt_1, axiom,
% 0.56/0.79    (![B:$i,A:$i]:
% 0.56/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.56/0.79  thf('15', plain,
% 0.56/0.79      (![X17 : $i, X18 : $i]:
% 0.56/0.79         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.56/0.79  thf(t113_zfmisc_1, axiom,
% 0.56/0.79    (![A:$i,B:$i]:
% 0.56/0.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.56/0.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.79  thf('16', plain,
% 0.56/0.79      (![X2 : $i, X3 : $i]:
% 0.56/0.79         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.56/0.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.56/0.79  thf('17', plain,
% 0.56/0.79      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['16'])).
% 0.56/0.79  thf('18', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.79         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.56/0.79      inference('sup+', [status(thm)], ['15', '17'])).
% 0.56/0.79  thf('19', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (m1_subset_1 @ X0 @ 
% 0.56/0.79             (k1_zfmisc_1 @ 
% 0.56/0.79              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.79  thf(l13_xboole_0, axiom,
% 0.56/0.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.56/0.79  thf('20', plain,
% 0.56/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.79  thf('21', plain,
% 0.56/0.79      (![X2 : $i, X3 : $i]:
% 0.56/0.79         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.56/0.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.56/0.79  thf('22', plain,
% 0.56/0.79      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['21'])).
% 0.56/0.79  thf(cc3_relset_1, axiom,
% 0.56/0.79    (![A:$i,B:$i]:
% 0.56/0.79     ( ( v1_xboole_0 @ A ) =>
% 0.56/0.79       ( ![C:$i]:
% 0.56/0.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.79           ( v1_xboole_0 @ C ) ) ) ))).
% 0.56/0.79  thf('23', plain,
% 0.56/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.56/0.79         (~ (v1_xboole_0 @ X8)
% 0.56/0.79          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 0.56/0.79          | (v1_xboole_0 @ X9))),
% 0.56/0.79      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.56/0.79  thf('24', plain,
% 0.56/0.79      (![X1 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79          | (v1_xboole_0 @ X1)
% 0.56/0.79          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.56/0.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.56/0.79  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.79  thf('26', plain,
% 0.56/0.79      (![X1 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79          | (v1_xboole_0 @ X1))),
% 0.56/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.56/0.79  thf('27', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.56/0.79          | ~ (v1_xboole_0 @ X0)
% 0.56/0.79          | (v1_xboole_0 @ X1))),
% 0.56/0.79      inference('sup-', [status(thm)], ['20', '26'])).
% 0.56/0.79  thf('28', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (v1_xboole_0 @ X0)
% 0.56/0.79          | ~ (v1_xboole_0 @ 
% 0.56/0.79               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['19', '27'])).
% 0.56/0.79  thf('29', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i]:
% 0.56/0.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.79          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 0.56/0.79          | (v1_xboole_0 @ X0)
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['18', '28'])).
% 0.56/0.79  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.79  thf('31', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i]:
% 0.56/0.79         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 0.56/0.79          | (v1_xboole_0 @ X0)
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.56/0.79  thf('32', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (m1_subset_1 @ X0 @ 
% 0.56/0.79             (k1_zfmisc_1 @ 
% 0.56/0.79              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.56/0.79  thf(zf_stmt_3, axiom,
% 0.56/0.79    (![C:$i,B:$i,A:$i]:
% 0.56/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.56/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.56/0.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.56/0.79  thf(zf_stmt_5, axiom,
% 0.56/0.79    (![A:$i,B:$i,C:$i]:
% 0.56/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.56/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.56/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.56/0.79  thf('33', plain,
% 0.56/0.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.79         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.56/0.79          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.56/0.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.56/0.79  thf('34', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.56/0.79  thf('35', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (v1_xboole_0 @ X0)
% 0.56/0.79          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['31', '34'])).
% 0.56/0.79  thf('36', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | (v1_xboole_0 @ X0)
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['35'])).
% 0.56/0.79  thf('37', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (m1_subset_1 @ X0 @ 
% 0.56/0.79             (k1_zfmisc_1 @ 
% 0.56/0.79              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.56/0.79    (![A:$i,B:$i,C:$i]:
% 0.56/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.56/0.79  thf('38', plain,
% 0.56/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.56/0.79         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.56/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.56/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.56/0.79  thf('39', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.56/0.79              = (k1_relat_1 @ X0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['37', '38'])).
% 0.56/0.79  thf('40', plain,
% 0.56/0.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.79         (((X19) != (k1_relset_1 @ X19 @ X20 @ X21))
% 0.56/0.79          | (v1_funct_2 @ X21 @ X19 @ X20)
% 0.56/0.79          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.56/0.79  thf('41', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0)
% 0.56/0.79          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['39', '40'])).
% 0.56/0.79  thf('42', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.56/0.79          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.56/0.79  thf('43', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (v1_xboole_0 @ X0)
% 0.56/0.79          | ~ (v1_relat_1 @ X0)
% 0.56/0.79          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['36', '42'])).
% 0.56/0.79  thf('44', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.56/0.79          | (v1_xboole_0 @ X0)
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['43'])).
% 0.56/0.79  thf('45', plain,
% 0.56/0.79      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.56/0.79      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.56/0.79  thf('46', plain, ((~ (v1_relat_1 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.56/0.79      inference('sup-', [status(thm)], ['44', '45'])).
% 0.56/0.79  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.79  thf('48', plain, ((v1_xboole_0 @ sk_A)),
% 0.56/0.79      inference('demod', [status(thm)], ['46', '47'])).
% 0.56/0.79  thf('49', plain,
% 0.56/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.79  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.79  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.79  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.79  thf('53', plain,
% 0.56/0.79      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.56/0.79          (k2_relat_1 @ k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['14', '50', '51', '52'])).
% 0.56/0.79  thf('54', plain,
% 0.56/0.79      (![X17 : $i, X18 : $i]:
% 0.56/0.79         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.56/0.79  thf('55', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.56/0.79  thf('56', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.56/0.79          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['54', '55'])).
% 0.56/0.79  thf('57', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.56/0.79          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.56/0.79  thf('58', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0)
% 0.56/0.79          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['56', '57'])).
% 0.56/0.79  thf('59', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.56/0.79          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['58'])).
% 0.56/0.79  thf('60', plain,
% 0.56/0.79      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.56/0.79          (k2_relat_1 @ k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['14', '50', '51', '52'])).
% 0.56/0.79  thf('61', plain,
% 0.56/0.79      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.56/0.79        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['59', '60'])).
% 0.56/0.79  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.79  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.79  thf('64', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.56/0.79      inference('demod', [status(thm)], ['62', '63'])).
% 0.56/0.79  thf('65', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['61', '64'])).
% 0.56/0.79  thf('66', plain,
% 0.56/0.79      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.56/0.79      inference('demod', [status(thm)], ['53', '65'])).
% 0.56/0.79  thf('67', plain,
% 0.56/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.79  thf('68', plain,
% 0.56/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.79  thf('69', plain,
% 0.56/0.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.79         (((X22) != (k1_xboole_0))
% 0.56/0.79          | ((X23) = (k1_xboole_0))
% 0.56/0.79          | (v1_funct_2 @ X24 @ X23 @ X22)
% 0.56/0.79          | ((X24) != (k1_xboole_0))
% 0.56/0.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.56/0.79  thf('70', plain,
% 0.56/0.79      (![X23 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.56/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ k1_xboole_0)))
% 0.56/0.79          | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)
% 0.56/0.79          | ((X23) = (k1_xboole_0)))),
% 0.56/0.79      inference('simplify', [status(thm)], ['69'])).
% 0.56/0.79  thf('71', plain,
% 0.56/0.79      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['16'])).
% 0.56/0.79  thf('72', plain,
% 0.56/0.79      (![X23 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79          | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)
% 0.56/0.79          | ((X23) = (k1_xboole_0)))),
% 0.56/0.79      inference('demod', [status(thm)], ['70', '71'])).
% 0.56/0.79  thf('73', plain,
% 0.56/0.79      ((![X23 : $i]:
% 0.56/0.79          (((X23) = (k1_xboole_0))
% 0.56/0.79           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))
% 0.56/0.79         <= ((![X23 : $i]:
% 0.56/0.79                (((X23) = (k1_xboole_0))
% 0.56/0.79                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.56/0.79      inference('split', [status(esa)], ['72'])).
% 0.56/0.79  thf('74', plain,
% 0.56/0.79      ((![X0 : $i, X1 : $i]:
% 0.56/0.79          ((v1_funct_2 @ X0 @ X1 @ k1_xboole_0)
% 0.56/0.79           | ~ (v1_xboole_0 @ X0)
% 0.56/0.79           | ((X1) = (k1_xboole_0))))
% 0.56/0.79         <= ((![X23 : $i]:
% 0.56/0.79                (((X23) = (k1_xboole_0))
% 0.56/0.79                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup+', [status(thm)], ['68', '73'])).
% 0.56/0.79  thf('75', plain,
% 0.56/0.79      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.79          ((v1_funct_2 @ X2 @ X1 @ X0)
% 0.56/0.79           | ~ (v1_xboole_0 @ X0)
% 0.56/0.79           | ((X1) = (k1_xboole_0))
% 0.56/0.79           | ~ (v1_xboole_0 @ X2)))
% 0.56/0.79         <= ((![X23 : $i]:
% 0.56/0.79                (((X23) = (k1_xboole_0))
% 0.56/0.79                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup+', [status(thm)], ['67', '74'])).
% 0.56/0.79  thf('76', plain,
% 0.56/0.79      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.56/0.79      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.56/0.79  thf('77', plain,
% 0.56/0.79      (((~ (v1_xboole_0 @ sk_A)
% 0.56/0.79         | ((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.56/0.79         | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_A))))
% 0.56/0.79         <= ((![X23 : $i]:
% 0.56/0.79                (((X23) = (k1_xboole_0))
% 0.56/0.79                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['75', '76'])).
% 0.56/0.79  thf('78', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.79         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.56/0.79      inference('sup+', [status(thm)], ['15', '17'])).
% 0.56/0.79  thf('79', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (m1_subset_1 @ X0 @ 
% 0.56/0.79             (k1_zfmisc_1 @ 
% 0.56/0.79              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.79  thf('80', plain,
% 0.56/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.79  thf('81', plain,
% 0.56/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.79  thf('82', plain,
% 0.56/0.79      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('split', [status(esa)], ['72'])).
% 0.56/0.79  thf('83', plain,
% 0.56/0.79      ((![X0 : $i]:
% 0.56/0.79          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79           | ~ (v1_xboole_0 @ X0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['81', '82'])).
% 0.56/0.79  thf('84', plain,
% 0.56/0.79      (![X1 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79          | (v1_xboole_0 @ X1))),
% 0.56/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.56/0.79  thf('85', plain,
% 0.56/0.79      ((![X0 : $i]: ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('clc', [status(thm)], ['83', '84'])).
% 0.56/0.79  thf('86', plain,
% 0.56/0.79      ((![X0 : $i, X1 : $i]:
% 0.56/0.79          (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['80', '85'])).
% 0.56/0.79  thf('87', plain,
% 0.56/0.79      ((![X0 : $i]:
% 0.56/0.79          (~ (v1_relat_1 @ X0)
% 0.56/0.79           | ~ (v1_xboole_0 @ 
% 0.56/0.79                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['79', '86'])).
% 0.56/0.79  thf('88', plain,
% 0.56/0.79      ((![X0 : $i, X1 : $i]:
% 0.56/0.79          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.79           | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 0.56/0.79           | ~ (v1_relat_1 @ X0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['78', '87'])).
% 0.56/0.79  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.79  thf('90', plain,
% 0.56/0.79      ((![X0 : $i, X1 : $i]:
% 0.56/0.79          ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1) | ~ (v1_relat_1 @ X0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('demod', [status(thm)], ['88', '89'])).
% 0.56/0.79  thf('91', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.56/0.79  thf('92', plain,
% 0.56/0.79      ((![X0 : $i]:
% 0.56/0.79          (~ (v1_relat_1 @ X0)
% 0.56/0.79           | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79           | ~ (v1_relat_1 @ X0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['90', '91'])).
% 0.56/0.79  thf('93', plain,
% 0.56/0.79      ((![X0 : $i]:
% 0.56/0.79          ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79           | ~ (v1_relat_1 @ X0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('simplify', [status(thm)], ['92'])).
% 0.56/0.79  thf('94', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.56/0.79          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.56/0.79          | ~ (v1_relat_1 @ X0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.56/0.79  thf('95', plain,
% 0.56/0.79      ((![X0 : $i]:
% 0.56/0.79          (~ (v1_relat_1 @ X0)
% 0.56/0.79           | ~ (v1_relat_1 @ X0)
% 0.56/0.79           | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['93', '94'])).
% 0.56/0.79  thf('96', plain,
% 0.56/0.79      ((![X0 : $i]:
% 0.56/0.79          ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.56/0.79           | ~ (v1_relat_1 @ X0)))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('simplify', [status(thm)], ['95'])).
% 0.56/0.79  thf('97', plain,
% 0.56/0.79      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.56/0.79      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.56/0.79  thf('98', plain,
% 0.56/0.79      ((~ (v1_relat_1 @ sk_A))
% 0.56/0.79         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['96', '97'])).
% 0.56/0.79  thf('99', plain, ((v1_relat_1 @ sk_A)),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.79  thf('100', plain,
% 0.56/0.79      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.56/0.79      inference('demod', [status(thm)], ['98', '99'])).
% 0.56/0.79  thf('101', plain,
% 0.56/0.79      ((![X23 : $i]:
% 0.56/0.79          (((X23) = (k1_xboole_0))
% 0.56/0.79           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))) | 
% 0.56/0.79       ~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.56/0.79      inference('split', [status(esa)], ['72'])).
% 0.56/0.79  thf('102', plain,
% 0.56/0.79      ((![X23 : $i]:
% 0.56/0.79          (((X23) = (k1_xboole_0))
% 0.56/0.79           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))),
% 0.56/0.79      inference('sat_resolution*', [status(thm)], ['100', '101'])).
% 0.56/0.79  thf('103', plain,
% 0.56/0.79      ((~ (v1_xboole_0 @ sk_A)
% 0.56/0.79        | ((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.56/0.79        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_A)))),
% 0.56/0.79      inference('simpl_trail', [status(thm)], ['77', '102'])).
% 0.56/0.79  thf('104', plain, ((v1_xboole_0 @ sk_A)),
% 0.56/0.79      inference('demod', [status(thm)], ['46', '47'])).
% 0.56/0.79  thf('105', plain,
% 0.56/0.79      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.56/0.79        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_A)))),
% 0.56/0.79      inference('demod', [status(thm)], ['103', '104'])).
% 0.56/0.79  thf('106', plain, (((sk_A) = (k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.79  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.79  thf('108', plain,
% 0.56/0.79      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.56/0.79        | ~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.56/0.79      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.56/0.79  thf('109', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['61', '64'])).
% 0.56/0.79  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.79  thf('111', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.56/0.79  thf('112', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.56/0.79      inference('demod', [status(thm)], ['66', '111'])).
% 0.56/0.79  thf('113', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['61', '64'])).
% 0.56/0.79  thf('114', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (~ (v1_relat_1 @ X0)
% 0.56/0.79          | (m1_subset_1 @ X0 @ 
% 0.56/0.79             (k1_zfmisc_1 @ 
% 0.56/0.79              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.56/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.79  thf('115', plain,
% 0.56/0.79      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.56/0.79         (k1_zfmisc_1 @ 
% 0.56/0.79          (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))
% 0.56/0.79        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.56/0.79      inference('sup+', [status(thm)], ['113', '114'])).
% 0.56/0.79  thf('116', plain,
% 0.56/0.79      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['16'])).
% 0.56/0.79  thf('117', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.56/0.79      inference('demod', [status(thm)], ['62', '63'])).
% 0.56/0.79  thf('118', plain,
% 0.56/0.79      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.56/0.79  thf('119', plain,
% 0.56/0.79      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['16'])).
% 0.56/0.79  thf('120', plain,
% 0.56/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.56/0.79         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.56/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.56/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.56/0.79  thf('121', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_relat_1 @ X1)))),
% 0.56/0.79      inference('sup-', [status(thm)], ['119', '120'])).
% 0.56/0.79  thf('122', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.56/0.79           = (k1_relat_1 @ k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['118', '121'])).
% 0.56/0.79  thf('123', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.56/0.79  thf('124', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['122', '123'])).
% 0.56/0.79  thf('125', plain,
% 0.56/0.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.79         (((X19) != (k1_relset_1 @ X19 @ X20 @ X21))
% 0.56/0.79          | (v1_funct_2 @ X21 @ X19 @ X20)
% 0.56/0.79          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.56/0.79  thf('126', plain,
% 0.56/0.79      (![X0 : $i]:
% 0.56/0.79         (((X0) != (k1_xboole_0))
% 0.56/0.79          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.56/0.79          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['124', '125'])).
% 0.56/0.79  thf('127', plain,
% 0.56/0.79      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.56/0.79        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['126'])).
% 0.56/0.79  thf('128', plain,
% 0.56/0.79      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.56/0.79  thf('129', plain,
% 0.56/0.79      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.56/0.79      inference('simplify', [status(thm)], ['21'])).
% 0.56/0.79  thf('130', plain,
% 0.56/0.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.79         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.56/0.79          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.56/0.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.56/0.79  thf('131', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.56/0.79          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.56/0.79      inference('sup-', [status(thm)], ['129', '130'])).
% 0.56/0.79  thf('132', plain,
% 0.56/0.79      (![X17 : $i, X18 : $i]:
% 0.56/0.79         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 0.56/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.56/0.79  thf('133', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 0.56/0.79      inference('simplify', [status(thm)], ['132'])).
% 0.56/0.79  thf('134', plain,
% 0.56/0.79      (![X0 : $i, X1 : $i]:
% 0.56/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.56/0.79          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.56/0.79      inference('demod', [status(thm)], ['131', '133'])).
% 0.56/0.79  thf('135', plain,
% 0.56/0.79      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.56/0.79      inference('sup-', [status(thm)], ['128', '134'])).
% 0.56/0.79  thf('136', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.56/0.79      inference('simplify_reflect+', [status(thm)], ['127', '135'])).
% 0.56/0.79  thf('137', plain, ($false), inference('demod', [status(thm)], ['112', '136'])).
% 0.56/0.79  
% 0.56/0.79  % SZS output end Refutation
% 0.56/0.79  
% 0.63/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
