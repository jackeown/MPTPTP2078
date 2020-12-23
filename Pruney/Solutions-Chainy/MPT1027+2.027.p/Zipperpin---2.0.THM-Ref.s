%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cmpglrUae0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 158 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  450 (1766 expanded)
%              Number of equality atoms :   37 (  96 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','14'])).

thf('16',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ( X21 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X20: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','21','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('29',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','38'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['17','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cmpglrUae0
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 126 iterations in 0.085s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(l13_xboole_0, axiom,
% 0.21/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf(d1_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, axiom,
% 0.21/0.51    (![B:$i,A:$i]:
% 0.21/0.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.51       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 0.21/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '2'])).
% 0.21/0.51  thf(t130_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.21/0.51         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.51           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.21/0.51            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.51              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_3, axiom,
% 0.21/0.51    (![C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_5, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.21/0.51          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.51        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.21/0.51          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.21/0.51          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((((sk_A) != (sk_A))
% 0.21/0.51        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.51        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.21/0.51        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('14', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.51  thf('15', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['10', '14'])).
% 0.21/0.51  thf('16', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '15'])).
% 0.21/0.51  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (((X19) != (k1_xboole_0))
% 0.21/0.51          | ((X20) = (k1_xboole_0))
% 0.21/0.51          | (v1_funct_2 @ X21 @ X20 @ X19)
% 0.21/0.51          | ((X21) != (k1_xboole_0))
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X20 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ k1_xboole_0)))
% 0.21/0.51          | (v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.21/0.51          | ((X20) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.51  thf(t113_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('22', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X8 : $i, X10 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X20 : $i]:
% 0.21/0.51         ((v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.21/0.51          | ((X20) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '21', '24'])).
% 0.21/0.51  thf('26', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '15'])).
% 0.21/0.51  thf('29', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf(cc4_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.51           ( v1_xboole_0 @ C ) ) ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ X11)
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 0.21/0.51          | (v1_xboole_0 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.21/0.51  thf('33', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('35', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.51  thf('36', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.51  thf(t69_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.51       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X3 @ X4)
% 0.21/0.51          | ~ (r1_tarski @ X3 @ X4)
% 0.21/0.51          | (v1_xboole_0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.51  thf('40', plain, ((v1_xboole_0 @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('42', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '42'])).
% 0.21/0.51  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '43'])).
% 0.21/0.51  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.51  thf('46', plain, ($false),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '44', '45'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
