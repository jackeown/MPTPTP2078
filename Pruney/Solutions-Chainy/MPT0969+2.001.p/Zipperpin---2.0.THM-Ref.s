%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yejGvq1eC9

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 (  90 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  468 ( 737 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t12_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_funct_2 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( zip_tseitin_2 @ X19 @ X21 @ X20 @ X23 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X21 != X19 )
      | ( ( k1_relat_1 @ X19 )
       != X23 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 )
      | ( zip_tseitin_2 @ X19 @ X19 @ X20 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','24','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    zip_tseitin_2 @ sk_B @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['12','28','29','30'])).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_2 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X25 @ X28 )
      | ( X28
       != ( k1_funct_2 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ ( k1_funct_2 @ X27 @ X26 ) )
      | ~ ( zip_tseitin_2 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k1_funct_2 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yejGvq1eC9
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 66 iterations in 0.050s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.51  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.51  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(t12_funct_2, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.51       ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.51            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.51          ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t12_funct_2])).
% 0.22/0.51  thf('0', plain, (~ (r2_hidden @ sk_B @ (k1_funct_2 @ sk_A @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc2_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         ((v5_relat_1 @ X5 @ X7)
% 0.22/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.51  thf('3', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf(d19_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v5_relat_1 @ X0 @ X1)
% 0.22/0.51          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc1_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( v1_relat_1 @ C ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((v1_relat_1 @ X2)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.51  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['5', '8'])).
% 0.22/0.51  thf(d2_funct_2, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.22/0.51       ( ![D:$i]:
% 0.22/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.51           ( ?[E:$i]:
% 0.22/0.51             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.22/0.51               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.22/0.51               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_1, axiom,
% 0.22/0.51    (![E:$i,D:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_2 @ E @ D @ B @ A ) <=>
% 0.22/0.51       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.22/0.51         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.22/0.51         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.22/0.51         ((zip_tseitin_2 @ X19 @ X21 @ X20 @ X23)
% 0.22/0.51          | ~ (v1_relat_1 @ X19)
% 0.22/0.51          | ~ (v1_funct_1 @ X19)
% 0.22/0.51          | ((X21) != (X19))
% 0.22/0.51          | ((k1_relat_1 @ X19) != (X23))
% 0.22/0.51          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.22/0.51          | ~ (v1_funct_1 @ X19)
% 0.22/0.51          | ~ (v1_relat_1 @ X19)
% 0.22/0.51          | (zip_tseitin_2 @ X19 @ X19 @ X20 @ (k1_relat_1 @ X19)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (((zip_tseitin_2 @ sk_B @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '11'])).
% 0.22/0.51  thf('13', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d1_funct_2, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_2, axiom,
% 0.22/0.51    (![C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.51         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.22/0.51          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.22/0.51          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 0.22/0.51        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_5, axiom,
% 0.22/0.51    (![B:$i,A:$i]:
% 0.22/0.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.51       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.51  thf(zf_stmt_6, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.51         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.22/0.51          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.51  thf('21', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 0.22/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.22/0.51      inference('sup+', [status(thm)], ['19', '21'])).
% 0.22/0.51  thf('23', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.22/0.51      inference('eq_fact', [status(thm)], ['22'])).
% 0.22/0.51  thf('24', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.22/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '24', '27'])).
% 0.22/0.51  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain, ((zip_tseitin_2 @ sk_B @ sk_B @ sk_A @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '28', '29', '30'])).
% 0.22/0.51  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_8, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.22/0.51       ( ![D:$i]:
% 0.22/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.51           ( ?[E:$i]: ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.51         (~ (zip_tseitin_2 @ X24 @ X25 @ X26 @ X27)
% 0.22/0.51          | (r2_hidden @ X25 @ X28)
% 0.22/0.51          | ((X28) != (k1_funct_2 @ X27 @ X26)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.51         ((r2_hidden @ X25 @ (k1_funct_2 @ X27 @ X26))
% 0.22/0.51          | ~ (zip_tseitin_2 @ X24 @ X25 @ X26 @ X27))),
% 0.22/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.51  thf('34', plain, ((r2_hidden @ sk_B @ (k1_funct_2 @ sk_A @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '33'])).
% 0.22/0.51  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
