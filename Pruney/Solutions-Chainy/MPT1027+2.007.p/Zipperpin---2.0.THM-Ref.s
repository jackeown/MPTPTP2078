%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DcMCNa6GzE

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 130 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  494 (1622 expanded)
%              Number of equality atoms :   25 (  63 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('2',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['9','12','13'])).

thf('15',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['6','14'])).

thf('16',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['4','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_partfun1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('19',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['22','23'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15
       != ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['6','14'])).

thf('40',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['29','41','42'])).

thf('44',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['26','43'])).

thf('45',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['19','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['16','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DcMCNa6GzE
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 81 iterations in 0.055s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(t130_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.51         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.51           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.51            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.51              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.20/0.51         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (v1_funct_1 @ X7)
% 0.20/0.51          | ~ (v1_partfun1 @ X7 @ X8)
% 0.20/0.51          | (v1_funct_2 @ X7 @ X8 @ X9)
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((v1_funct_2 @ sk_C @ sk_A @ sk_B) | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.20/0.51         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('9', plain, (((v1_funct_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.20/0.51       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.20/0.51       ~ ((v1_funct_1 @ sk_C))),
% 0.20/0.51      inference('split', [status(esa)], ['5'])).
% 0.20/0.51  thf('14', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['9', '12', '13'])).
% 0.20/0.51  thf('15', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['6', '14'])).
% 0.20/0.51  thf('16', plain, (~ (v1_partfun1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['4', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_partfun1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 0.20/0.51          | (v1_partfun1 @ X11 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.20/0.51  thf('19', plain, (((v1_partfun1 @ sk_C @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.20/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf(fc10_relat_1, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.20/0.51  thf('26', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc4_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.51           ( v1_xboole_0 @ C ) ) ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.20/0.51          | (v1_xboole_0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.20/0.51  thf('29', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf(d1_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, axiom,
% 0.20/0.51    (![B:$i,A:$i]:
% 0.20/0.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_5, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.20/0.51          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.51  thf('35', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (((X15) != (k1_relset_1 @ X15 @ X16 @ X17))
% 0.20/0.51          | (v1_funct_2 @ X17 @ X15 @ X16)
% 0.20/0.51          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      ((((sk_A) != (sk_A))
% 0.20/0.51        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.20/0.51        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.51  thf('39', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['6', '14'])).
% 0.20/0.51  thf('40', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '40'])).
% 0.20/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.51  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.51  thf('43', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '41', '42'])).
% 0.20/0.51  thf('44', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '43'])).
% 0.20/0.51  thf('45', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '44'])).
% 0.20/0.51  thf('46', plain, ($false), inference('demod', [status(thm)], ['16', '45'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
