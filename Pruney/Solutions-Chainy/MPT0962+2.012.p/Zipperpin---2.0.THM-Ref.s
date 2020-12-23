%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iLCnNy53Hi

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:50 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 630 expanded)
%              Number of leaves         :   28 ( 179 expanded)
%              Depth                    :   16
%              Number of atoms          :  612 (7544 expanded)
%              Number of equality atoms :   43 ( 174 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X18 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('27',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','38'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ( X26 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('47',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45','48'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('54',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('55',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('58',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('59',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['42','56','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iLCnNy53Hi
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:59:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 183 iterations in 0.150s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(t4_funct_2, conjecture,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.41/0.60         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.41/0.60           ( m1_subset_1 @
% 0.41/0.60             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i]:
% 0.41/0.60        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.41/0.60            ( ( v1_funct_1 @ B ) & 
% 0.41/0.60              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.41/0.60              ( m1_subset_1 @
% 0.41/0.60                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.41/0.60  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.41/0.60  thf(t11_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ C ) =>
% 0.41/0.60       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.41/0.60           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.41/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X16) @ X18)
% 0.41/0.60          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.41/0.60          | ~ (v1_relat_1 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X0)
% 0.41/0.60          | (m1_subset_1 @ X0 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.41/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (((m1_subset_1 @ sk_B @ 
% 0.41/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '4'])).
% 0.41/0.60  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf(d1_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.60  thf(zf_stmt_2, axiom,
% 0.41/0.60    (![C:$i,B:$i,A:$i]:
% 0.41/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.60  thf(zf_stmt_4, axiom,
% 0.41/0.60    (![B:$i,A:$i]:
% 0.41/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.60  thf(zf_stmt_5, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.60         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.41/0.60          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.41/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.41/0.60        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.60         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.41/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.60         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 0.41/0.60          | (v1_funct_2 @ X23 @ X21 @ X22)
% 0.41/0.60          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.41/0.60        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.41/0.60        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.41/0.60        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      ((~ (v1_funct_1 @ sk_B)
% 0.41/0.60        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.41/0.60        | ~ (m1_subset_1 @ sk_B @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.41/0.60         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['16'])).
% 0.41/0.60  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['16'])).
% 0.41/0.60  thf('20', plain, (((v1_funct_1 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      ((~ (m1_subset_1 @ sk_B @ 
% 0.41/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.41/0.60         <= (~
% 0.41/0.60             ((m1_subset_1 @ sk_B @ 
% 0.41/0.60               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.41/0.60      inference('split', [status(esa)], ['16'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (((m1_subset_1 @ sk_B @ 
% 0.41/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.41/0.60       ~
% 0.41/0.60       ((m1_subset_1 @ sk_B @ 
% 0.41/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.41/0.60       ~ ((v1_funct_1 @ sk_B))),
% 0.41/0.60      inference('split', [status(esa)], ['16'])).
% 0.41/0.60  thf('25', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['20', '23', '24'])).
% 0.41/0.60  thf('26', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.41/0.60  thf('27', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('clc', [status(thm)], ['15', '26'])).
% 0.41/0.60  thf('28', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('clc', [status(thm)], ['9', '27'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X19 : $i, X20 : $i]:
% 0.41/0.60         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.60  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('clc', [status(thm)], ['9', '27'])).
% 0.41/0.60  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('32', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf(t3_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]:
% 0.41/0.60         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf(t113_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.41/0.60  thf('39', plain, ((r1_tarski @ sk_B @ k1_xboole_0)),
% 0.41/0.60      inference('demod', [status(thm)], ['35', '36', '38'])).
% 0.41/0.60  thf(t3_xboole_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.41/0.60  thf('41', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['32', '41'])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.60         (((X24) != (k1_xboole_0))
% 0.41/0.60          | ((X25) = (k1_xboole_0))
% 0.41/0.60          | (v1_funct_2 @ X26 @ X25 @ X24)
% 0.41/0.60          | ((X26) != (k1_xboole_0))
% 0.41/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X25 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ k1_xboole_0)))
% 0.41/0.60          | (v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0)
% 0.41/0.60          | ((X25) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.41/0.60  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X7 : $i, X9 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X25 : $i]:
% 0.41/0.60         ((v1_funct_2 @ k1_xboole_0 @ X25 @ k1_xboole_0)
% 0.41/0.60          | ((X25) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['44', '45', '48'])).
% 0.41/0.60  thf('50', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.41/0.60  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('52', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.41/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf('53', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('54', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.41/0.60      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.41/0.60  thf('56', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['49', '55'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (![X19 : $i, X20 : $i]:
% 0.41/0.60         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (![X19 : $i, X20 : $i]:
% 0.41/0.60         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.60  thf('59', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 0.41/0.60      inference('simplify', [status(thm)], ['58'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.41/0.60      inference('sup+', [status(thm)], ['57', '59'])).
% 0.41/0.60  thf('61', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.41/0.60      inference('eq_fact', [status(thm)], ['60'])).
% 0.41/0.60  thf('62', plain, ($false),
% 0.41/0.60      inference('demod', [status(thm)], ['42', '56', '61'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
