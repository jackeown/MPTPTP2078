%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gYKTDrXDLw

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:06 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 113 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  419 (1008 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('15',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X25 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X25 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X5 @ X6 ) @ X6 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','26'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X15: $i] :
      ( ( ( k2_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gYKTDrXDLw
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:25:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.34/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.55  % Solved by: fo/fo7.sh
% 0.34/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.55  % done 60 iterations in 0.052s
% 0.34/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.55  % SZS output start Refutation
% 0.34/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.34/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.34/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.34/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.34/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.55  thf(t49_relset_1, conjecture,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.55       ( ![B:$i]:
% 0.34/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.34/0.55           ( ![C:$i]:
% 0.34/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.34/0.55                    ( ![D:$i]:
% 0.34/0.55                      ( ( m1_subset_1 @ D @ B ) =>
% 0.34/0.55                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.55    (~( ![A:$i]:
% 0.34/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.55          ( ![B:$i]:
% 0.34/0.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.34/0.55              ( ![C:$i]:
% 0.34/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.34/0.55                       ( ![D:$i]:
% 0.34/0.55                         ( ( m1_subset_1 @ D @ B ) =>
% 0.34/0.55                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.34/0.55    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.34/0.55  thf('0', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(cc2_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.55  thf('1', plain,
% 0.34/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.55         ((v5_relat_1 @ X16 @ X18)
% 0.34/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.34/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.55  thf('2', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.34/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.55  thf(d19_relat_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( v1_relat_1 @ B ) =>
% 0.34/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.55  thf('3', plain,
% 0.34/0.55      (![X11 : $i, X12 : $i]:
% 0.34/0.55         (~ (v5_relat_1 @ X11 @ X12)
% 0.34/0.55          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.34/0.55          | ~ (v1_relat_1 @ X11))),
% 0.34/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.34/0.55  thf('4', plain,
% 0.34/0.55      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.34/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.55  thf('5', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(cc2_relat_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( v1_relat_1 @ A ) =>
% 0.34/0.55       ( ![B:$i]:
% 0.34/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.34/0.55  thf('6', plain,
% 0.34/0.55      (![X9 : $i, X10 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.34/0.55          | (v1_relat_1 @ X9)
% 0.34/0.55          | ~ (v1_relat_1 @ X10))),
% 0.34/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.34/0.55  thf('7', plain,
% 0.34/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.34/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.55  thf(fc6_relat_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.55  thf('8', plain,
% 0.34/0.55      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.34/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.55  thf('9', plain, ((v1_relat_1 @ sk_C_2)),
% 0.34/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.34/0.55  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.34/0.55      inference('demod', [status(thm)], ['4', '9'])).
% 0.34/0.55  thf(d1_zfmisc_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.34/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.34/0.55  thf('11', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.34/0.55          | (r2_hidden @ X0 @ X2)
% 0.34/0.55          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.34/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.34/0.55  thf('12', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i]:
% 0.34/0.55         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.34/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.34/0.55  thf('13', plain,
% 0.34/0.55      ((r2_hidden @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.34/0.55      inference('sup-', [status(thm)], ['10', '12'])).
% 0.34/0.55  thf(t1_subset, axiom,
% 0.34/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.34/0.55  thf('14', plain,
% 0.34/0.55      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.34/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.34/0.55  thf('15', plain,
% 0.34/0.55      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.34/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.55  thf(t10_subset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.55       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.55            ( ![C:$i]:
% 0.34/0.55              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.34/0.55  thf('16', plain,
% 0.34/0.55      (![X5 : $i, X6 : $i]:
% 0.34/0.55         ((r2_hidden @ (sk_C_1 @ X5 @ X6) @ X5)
% 0.34/0.55          | ((X5) = (k1_xboole_0))
% 0.34/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.34/0.55      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.34/0.55  thf('17', plain,
% 0.34/0.55      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.34/0.55        | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ 
% 0.34/0.55           (k2_relat_1 @ sk_C_2)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.55  thf('18', plain,
% 0.34/0.55      (![X25 : $i]:
% 0.34/0.55         (~ (r2_hidden @ X25 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 0.34/0.55          | ~ (m1_subset_1 @ X25 @ sk_B))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('19', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.34/0.55  thf('20', plain,
% 0.34/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.55         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.34/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.34/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.34/0.55  thf('21', plain,
% 0.34/0.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.34/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.55  thf('22', plain,
% 0.34/0.55      (![X25 : $i]:
% 0.34/0.55         (~ (r2_hidden @ X25 @ (k2_relat_1 @ sk_C_2))
% 0.34/0.55          | ~ (m1_subset_1 @ X25 @ sk_B))),
% 0.34/0.55      inference('demod', [status(thm)], ['18', '21'])).
% 0.34/0.55  thf('23', plain,
% 0.34/0.55      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.34/0.55        | ~ (m1_subset_1 @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B))),
% 0.34/0.55      inference('sup-', [status(thm)], ['17', '22'])).
% 0.34/0.55  thf('24', plain,
% 0.34/0.55      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.34/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.55  thf('25', plain,
% 0.34/0.55      (![X5 : $i, X6 : $i]:
% 0.34/0.55         ((m1_subset_1 @ (sk_C_1 @ X5 @ X6) @ X6)
% 0.34/0.55          | ((X5) = (k1_xboole_0))
% 0.34/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.34/0.55      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.34/0.55  thf('26', plain,
% 0.34/0.55      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.34/0.55        | (m1_subset_1 @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B))),
% 0.34/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.34/0.55  thf('27', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.34/0.55      inference('clc', [status(thm)], ['23', '26'])).
% 0.34/0.55  thf(t65_relat_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( v1_relat_1 @ A ) =>
% 0.34/0.55       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.55         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.55  thf('28', plain,
% 0.34/0.55      (![X15 : $i]:
% 0.34/0.55         (((k2_relat_1 @ X15) != (k1_xboole_0))
% 0.34/0.55          | ((k1_relat_1 @ X15) = (k1_xboole_0))
% 0.34/0.55          | ~ (v1_relat_1 @ X15))),
% 0.34/0.55      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.34/0.55  thf('29', plain,
% 0.34/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.55        | ~ (v1_relat_1 @ sk_C_2)
% 0.34/0.55        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.55  thf('30', plain, ((v1_relat_1 @ sk_C_2)),
% 0.34/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.34/0.55  thf('31', plain,
% 0.34/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.55        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.34/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.34/0.55  thf('32', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.34/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.34/0.55  thf('33', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) != (k1_xboole_0))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('34', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.34/0.55  thf('35', plain,
% 0.34/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.55         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.34/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.34/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.34/0.55  thf('36', plain,
% 0.34/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.34/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.55  thf('37', plain, (((k1_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 0.34/0.55      inference('demod', [status(thm)], ['33', '36'])).
% 0.34/0.55  thf('38', plain, ($false),
% 0.34/0.55      inference('simplify_reflect-', [status(thm)], ['32', '37'])).
% 0.34/0.55  
% 0.34/0.55  % SZS output end Refutation
% 0.34/0.55  
% 0.34/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
