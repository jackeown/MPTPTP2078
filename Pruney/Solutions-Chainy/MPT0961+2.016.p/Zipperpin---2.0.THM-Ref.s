%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C6Cp0Svk70

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:40 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 529 expanded)
%              Number of leaves         :   28 ( 154 expanded)
%              Depth                    :   14
%              Number of atoms          :  752 (5854 expanded)
%              Number of equality atoms :   49 ( 216 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X19 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

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

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

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

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) @ sk_A )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['42','44','45','46','47','48'])).

thf('50',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['42','44','45','46','47','48'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['61','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['35','49','50','51','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C6Cp0Svk70
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:04:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 176 iterations in 0.162s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(t3_funct_2, conjecture,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ( v1_funct_1 @ A ) & 
% 0.38/0.62         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.38/0.62         ( m1_subset_1 @
% 0.38/0.62           A @ 
% 0.38/0.62           ( k1_zfmisc_1 @
% 0.38/0.62             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i]:
% 0.38/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62          ( ( v1_funct_1 @ A ) & 
% 0.38/0.62            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.38/0.62            ( m1_subset_1 @
% 0.38/0.62              A @ 
% 0.38/0.62              ( k1_zfmisc_1 @
% 0.38/0.62                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ sk_A)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.38/0.62        | ~ (m1_subset_1 @ sk_A @ 
% 0.38/0.62             (k1_zfmisc_1 @ 
% 0.38/0.62              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(d10_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.62  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.62  thf(t11_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ C ) =>
% 0.38/0.62       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.38/0.62           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.38/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.62         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.38/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ X19)
% 0.38/0.62          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.38/0.62          | ~ (v1_relat_1 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (m1_subset_1 @ X0 @ 
% 0.38/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.38/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X0 @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      ((~ (m1_subset_1 @ sk_A @ 
% 0.38/0.62           (k1_zfmisc_1 @ 
% 0.38/0.62            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.38/0.62         <= (~
% 0.38/0.62             ((m1_subset_1 @ sk_A @ 
% 0.38/0.62               (k1_zfmisc_1 @ 
% 0.38/0.62                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_A))
% 0.38/0.62         <= (~
% 0.38/0.62             ((m1_subset_1 @ sk_A @ 
% 0.38/0.62               (k1_zfmisc_1 @ 
% 0.38/0.62                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (((m1_subset_1 @ sk_A @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.38/0.62       ~
% 0.38/0.62       ((m1_subset_1 @ sk_A @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.38/0.62       ~ ((v1_funct_1 @ sk_A))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.38/0.62      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.38/0.62  thf(d1_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_1, axiom,
% 0.38/0.62    (![B:$i,A:$i]:
% 0.38/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X0 @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_3, axiom,
% 0.38/0.62    (![C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_5, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.62         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.38/0.62          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.38/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.38/0.62          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '21'])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X0 @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.62         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.38/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.38/0.62              = (k1_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.38/0.62          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.38/0.62          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.38/0.62          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.62          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '28'])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf('35', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.38/0.62      inference('demod', [status(thm)], ['17', '34'])).
% 0.38/0.62  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X0 @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.62  thf(t3_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i]:
% 0.38/0.62         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r1_tarski @ X0 @ 
% 0.38/0.62             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X0 : $i, X2 : $i]:
% 0.38/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (r1_tarski @ 
% 0.38/0.62               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.38/0.62          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0) @ sk_A)
% 0.38/0.62        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) = (sk_A))
% 0.38/0.62        | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['36', '41'])).
% 0.38/0.62  thf(t113_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.62  thf('45', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf('46', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.62  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('49', plain, (((k1_xboole_0) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['42', '44', '45', '46', '47', '48'])).
% 0.38/0.62  thf('50', plain, (((k1_xboole_0) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['42', '44', '45', '46', '47', '48'])).
% 0.38/0.62  thf(t60_relat_1, axiom,
% 0.38/0.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.62  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X7 : $i, X9 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.62         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.38/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.62  thf('57', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.62  thf('59', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.38/0.62          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.38/0.62          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((X1) != (k1_xboole_0))
% 0.38/0.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.38/0.62          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.62  thf('63', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.38/0.62      inference('simplify', [status(thm)], ['62'])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.62         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.38/0.62          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.38/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.62  thf('66', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['63', '66'])).
% 0.38/0.62  thf('68', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('demod', [status(thm)], ['61', '67'])).
% 0.38/0.62  thf('69', plain, ($false),
% 0.38/0.62      inference('demod', [status(thm)], ['35', '49', '50', '51', '68'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
