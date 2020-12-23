%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aXMtt6BX3A

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:38 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 771 expanded)
%              Number of leaves         :   30 ( 216 expanded)
%              Depth                    :   19
%              Number of atoms          :  811 (8566 expanded)
%              Number of equality atoms :   45 ( 323 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X11 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
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

thf('38',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X17 ) ) )
      | ( v1_partfun1 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('46',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_partfun1 @ sk_A @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','40','41'])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_partfun1 @ X12 @ X13 )
      | ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_partfun1 @ sk_A @ X0 )
      | ( v1_funct_2 @ sk_A @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_partfun1 @ sk_A @ X0 )
      | ( v1_funct_2 @ sk_A @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','40','41'])).

thf('61',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_A @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','40','41'])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_A )
      = ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','67','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','56'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['35','73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aXMtt6BX3A
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 117 iterations in 0.134s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(t3_funct_2, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57       ( ( v1_funct_1 @ A ) & 
% 0.36/0.57         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.36/0.57         ( m1_subset_1 @
% 0.36/0.57           A @ 
% 0.36/0.57           ( k1_zfmisc_1 @
% 0.36/0.57             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57          ( ( v1_funct_1 @ A ) & 
% 0.36/0.57            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.36/0.57            ( m1_subset_1 @
% 0.36/0.57              A @ 
% 0.36/0.57              ( k1_zfmisc_1 @
% 0.36/0.57                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      ((~ (v1_funct_1 @ sk_A)
% 0.36/0.57        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.36/0.57        | ~ (m1_subset_1 @ sk_A @ 
% 0.36/0.57             (k1_zfmisc_1 @ 
% 0.36/0.57              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.36/0.57         <= (~
% 0.36/0.57             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.57  thf(d10_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.57  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.57  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.57  thf(t11_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ C ) =>
% 0.36/0.57       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.36/0.57           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.36/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.57         (~ (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.36/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X9) @ X11)
% 0.36/0.57          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.36/0.57          | ~ (v1_relat_1 @ X9))),
% 0.36/0.57      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | (m1_subset_1 @ X0 @ 
% 0.36/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.36/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X0 @ 
% 0.36/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      ((~ (m1_subset_1 @ sk_A @ 
% 0.36/0.57           (k1_zfmisc_1 @ 
% 0.36/0.57            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.36/0.57         <= (~
% 0.36/0.57             ((m1_subset_1 @ sk_A @ 
% 0.36/0.57               (k1_zfmisc_1 @ 
% 0.36/0.57                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_A))
% 0.36/0.57         <= (~
% 0.36/0.57             ((m1_subset_1 @ sk_A @ 
% 0.36/0.57               (k1_zfmisc_1 @ 
% 0.36/0.57                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_A @ 
% 0.36/0.57         (k1_zfmisc_1 @ 
% 0.36/0.57          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.36/0.57       ~
% 0.36/0.57       ((m1_subset_1 @ sk_A @ 
% 0.36/0.57         (k1_zfmisc_1 @ 
% 0.36/0.57          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.36/0.57       ~ ((v1_funct_1 @ sk_A))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.36/0.57  thf(d1_funct_2, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_1, axiom,
% 0.36/0.57    (![B:$i,A:$i]:
% 0.36/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      (![X18 : $i, X19 : $i]:
% 0.36/0.57         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X0 @ 
% 0.36/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.36/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.57  thf(zf_stmt_3, axiom,
% 0.36/0.57    (![C:$i,B:$i,A:$i]:
% 0.36/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.57  thf(zf_stmt_5, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.57         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.36/0.57          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.36/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.57          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.36/0.57          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X0 @ 
% 0.36/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.36/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.57         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.36/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.36/0.57              = (k1_relat_1 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.57  thf('26', plain,
% 0.36/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.57         (((X20) != (k1_relset_1 @ X20 @ X21 @ X22))
% 0.36/0.57          | (v1_funct_2 @ X22 @ X20 @ X21)
% 0.36/0.57          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.57  thf('27', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.57          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.36/0.57          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['22', '28'])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.36/0.57          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('35', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.36/0.57      inference('demod', [status(thm)], ['17', '34'])).
% 0.36/0.57  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X0 @ 
% 0.36/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_A @ 
% 0.36/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0)))
% 0.36/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.57      inference('sup+', [status(thm)], ['36', '37'])).
% 0.36/0.57  thf(t113_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      (![X4 : $i, X5 : $i]:
% 0.36/0.57         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.57  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('42', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '40', '41'])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X4 : $i, X5 : $i]:
% 0.36/0.57         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.57  thf(cc1_partfun1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.57       ( ![C:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.57         (~ (v1_xboole_0 @ X15)
% 0.36/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X17)))
% 0.36/0.57          | (v1_partfun1 @ X16 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (![X1 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.36/0.57          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.36/0.57          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.57  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (![X1 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.36/0.57          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.57  thf('49', plain, ((v1_partfun1 @ sk_A @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['42', '48'])).
% 0.36/0.57  thf('50', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '40', '41'])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.57  thf(cc1_funct_2, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.36/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.57         (~ (v1_funct_1 @ X12)
% 0.36/0.57          | ~ (v1_partfun1 @ X12 @ X13)
% 0.36/0.57          | (v1_funct_2 @ X12 @ X13 @ X14)
% 0.36/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.36/0.57          | (v1_funct_2 @ X1 @ X0 @ k1_xboole_0)
% 0.36/0.57          | ~ (v1_partfun1 @ X1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_funct_1 @ sk_A)
% 0.36/0.57          | ~ (v1_partfun1 @ sk_A @ X0)
% 0.36/0.57          | (v1_funct_2 @ sk_A @ X0 @ k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['50', '53'])).
% 0.36/0.57  thf('55', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_partfun1 @ sk_A @ X0) | (v1_funct_2 @ sk_A @ X0 @ k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.57  thf('57', plain, ((v1_funct_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['49', '56'])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.57         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.36/0.57          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.36/0.57          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.57  thf('59', plain,
% 0.36/0.57      ((~ (zip_tseitin_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0)
% 0.36/0.57        | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.57  thf('60', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '40', '41'])).
% 0.36/0.57  thf('61', plain,
% 0.36/0.57      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.57  thf('62', plain,
% 0.36/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.57         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.36/0.57          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.36/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.36/0.57          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.36/0.57          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      (![X18 : $i, X19 : $i]:
% 0.36/0.57         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.57  thf('65', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 0.36/0.57      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.57  thf('66', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.36/0.57          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['63', '65'])).
% 0.36/0.57  thf('67', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_A @ X0 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['60', '66'])).
% 0.36/0.57  thf('68', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '40', '41'])).
% 0.36/0.57  thf('69', plain,
% 0.36/0.57      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.57  thf('70', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.57         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.36/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.57  thf('71', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.36/0.57          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.57  thf('72', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_A) = (k1_relat_1 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['68', '71'])).
% 0.36/0.57  thf('73', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['59', '67', '72'])).
% 0.36/0.57  thf('74', plain, ((v1_funct_2 @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['49', '56'])).
% 0.36/0.57  thf('75', plain, ($false),
% 0.36/0.57      inference('demod', [status(thm)], ['35', '73', '74'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
