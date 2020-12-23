%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3s6pTrHQfI

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 156 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  536 (1807 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X9 )
      | ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12
       != ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X18: $i] :
      ( ( v1_funct_2 @ X18 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('43',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['24','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3s6pTrHQfI
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 80 iterations in 0.056s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(t4_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.51         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.51           ( m1_subset_1 @
% 0.21/0.51             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.51            ( ( v1_funct_1 @ B ) & 
% 0.21/0.51              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.51              ( m1_subset_1 @
% 0.21/0.51                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.21/0.51  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.51  thf(t11_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.51           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.21/0.51          | ~ (r1_tarski @ (k2_relat_1 @ X7) @ X9)
% 0.21/0.51          | (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (m1_subset_1 @ X0 @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.21/0.51          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_B @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.51  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.21/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(d1_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, axiom,
% 0.21/0.51    (![C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (((X12) != (k1_relset_1 @ X12 @ X13 @ X14))
% 0.21/0.51          | (v1_funct_2 @ X14 @ X12 @ X13)
% 0.21/0.51          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.21/0.51        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.21/0.51        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.51         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['13'])).
% 0.21/0.51  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['13'])).
% 0.21/0.51  thf('17', plain, (((v1_funct_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((~ (m1_subset_1 @ sk_B @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ sk_B @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.21/0.51      inference('split', [status(esa)], ['13'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_B @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.21/0.51       ~
% 0.21/0.51       ((m1_subset_1 @ sk_B @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.21/0.51       ~ ((v1_funct_1 @ sk_B))),
% 0.21/0.51      inference('split', [status(esa)], ['13'])).
% 0.21/0.51  thf('22', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.21/0.51  thf('23', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.21/0.51  thf('24', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['12', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_4, axiom,
% 0.21/0.51    (![B:$i,A:$i]:
% 0.21/0.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.51       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.51  thf(zf_stmt_5, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.21/0.51          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.21/0.51        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i]:
% 0.21/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.21/0.51        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.51  thf(t3_funct_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ( v1_funct_1 @ A ) & 
% 0.21/0.51         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           A @ 
% 0.21/0.51           ( k1_zfmisc_1 @
% 0.21/0.51             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X18 : $i]:
% 0.21/0.51         ((v1_funct_2 @ X18 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18))
% 0.21/0.51          | ~ (v1_funct_1 @ X18)
% 0.21/0.51          | ~ (v1_relat_1 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51          | (zip_tseitin_0 @ sk_A @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51          | (zip_tseitin_0 @ sk_A @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.51         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['13'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      ((![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0))
% 0.21/0.51         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.21/0.51  thf('43', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '43'])).
% 0.21/0.51  thf('45', plain, ($false), inference('demod', [status(thm)], ['24', '44'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
