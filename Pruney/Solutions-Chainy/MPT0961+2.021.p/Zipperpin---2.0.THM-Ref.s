%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyr6lPpotE

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:41 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  110 (2016 expanded)
%              Number of leaves         :   27 ( 546 expanded)
%              Depth                    :   17
%              Number of atoms          :  828 (22996 expanded)
%              Number of equality atoms :   54 ( 830 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X20 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
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

thf('51',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','49','50'])).

thf('52',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ( X28 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X27 @ k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('55',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X27: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X27 @ k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54','57'])).

thf('59',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','49','50'])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('68',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('79',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('80',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['61','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyr6lPpotE
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:32:53 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 210 iterations in 0.176s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(t3_funct_2, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v1_funct_1 @ A ) & 
% 0.46/0.65         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.46/0.65         ( m1_subset_1 @
% 0.46/0.65           A @ 
% 0.46/0.65           ( k1_zfmisc_1 @
% 0.46/0.65             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65          ( ( v1_funct_1 @ A ) & 
% 0.46/0.65            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.46/0.65            ( m1_subset_1 @
% 0.46/0.65              A @ 
% 0.46/0.65              ( k1_zfmisc_1 @
% 0.46/0.65                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ sk_A)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.46/0.65        | ~ (m1_subset_1 @ sk_A @ 
% 0.46/0.65             (k1_zfmisc_1 @ 
% 0.46/0.65              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf(d10_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.65      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.65  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.65      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.65  thf(t11_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ C ) =>
% 0.46/0.65       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.46/0.65           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.46/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.65         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.46/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X18) @ X20)
% 0.46/0.65          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.46/0.65          | ~ (v1_relat_1 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | (m1_subset_1 @ X0 @ 
% 0.46/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.46/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X0 @ 
% 0.46/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      ((~ (m1_subset_1 @ sk_A @ 
% 0.46/0.65           (k1_zfmisc_1 @ 
% 0.46/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.46/0.65         <= (~
% 0.46/0.65             ((m1_subset_1 @ sk_A @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_A))
% 0.46/0.65         <= (~
% 0.46/0.65             ((m1_subset_1 @ sk_A @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_A @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.46/0.65       ~
% 0.46/0.65       ((m1_subset_1 @ sk_A @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.46/0.65       ~ ((v1_funct_1 @ sk_A))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.46/0.65  thf(d1_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_1, axiom,
% 0.46/0.65    (![B:$i,A:$i]:
% 0.46/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X0 @ 
% 0.46/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_3, axiom,
% 0.46/0.65    (![C:$i,B:$i,A:$i]:
% 0.46/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_5, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.46/0.65          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.46/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['18', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X0 @ 
% 0.46/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.46/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.46/0.65              = (k1_relat_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 0.46/0.65          | (v1_funct_2 @ X25 @ X23 @ X24)
% 0.46/0.65          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.65          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.65          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['17', '34'])).
% 0.46/0.65  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X0 @ 
% 0.46/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.65  thf(t3_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | (r1_tarski @ X0 @ 
% 0.46/0.65             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X0 : $i, X2 : $i]:
% 0.46/0.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (r1_tarski @ 
% 0.46/0.65               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.46/0.65          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0) @ sk_A)
% 0.46/0.65        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) = (sk_A))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['36', '41'])).
% 0.46/0.65  thf(t113_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i]:
% 0.46/0.65         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.65  thf('45', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('46', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.66  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('49', plain, (((k1_xboole_0) = (sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['42', '44', '45', '46', '47', '48'])).
% 0.46/0.66  thf('50', plain, (((k1_xboole_0) = (sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['42', '44', '45', '46', '47', '48'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         (((X26) != (k1_xboole_0))
% 0.46/0.66          | ((X27) = (k1_xboole_0))
% 0.46/0.66          | (v1_funct_2 @ X28 @ X27 @ X26)
% 0.46/0.66          | ((X28) != (k1_xboole_0))
% 0.46/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X27 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.46/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ k1_xboole_0)))
% 0.46/0.66          | (v1_funct_2 @ k1_xboole_0 @ X27 @ k1_xboole_0)
% 0.46/0.66          | ((X27) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.66  thf('55', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X7 : $i, X9 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X27 : $i]:
% 0.46/0.66         ((v1_funct_2 @ k1_xboole_0 @ X27 @ k1_xboole_0)
% 0.46/0.66          | ((X27) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54', '57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '49', '50'])).
% 0.46/0.66  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('61', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['51', '60'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('64', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 0.46/0.66      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.46/0.66      inference('sup+', [status(thm)], ['62', '64'])).
% 0.46/0.66  thf('66', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.46/0.66      inference('eq_fact', [status(thm)], ['65'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.46/0.66          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.46/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.66  thf('70', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['66', '69'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.66         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.46/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.66         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 0.46/0.66          | (v1_funct_2 @ X25 @ X23 @ X24)
% 0.46/0.66          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.46/0.66          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.46/0.66        (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['70', '76'])).
% 0.46/0.66  thf('78', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('79', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('80', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.46/0.66  thf('81', plain, ($false), inference('demod', [status(thm)], ['61', '80'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
