%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RECZYE5ZiW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 103 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  449 ( 920 expanded)
%              Number of equality atoms :   30 (  49 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v4_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['12','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('25',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X27 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
    | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 ) @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('31',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','29','30'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['23','31'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','37'])).

thf('39',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RECZYE5ZiW
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 68 iterations in 0.038s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(t50_relset_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.50               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50                    ( ![D:$i]:
% 0.20/0.50                      ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.50                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.50                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50                       ( ![D:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.50                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.50         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.20/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('3', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf(t2_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.50       ( ( A ) = ( B ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (((X5) = (X4))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_tarski])).
% 0.20/0.50  thf(t7_ordinal1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.20/0.50          | ((X0) = (X1))
% 0.20/0.50          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_xboole_0) = (X0))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X18 @ X19)
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('10', plain, ((v4_relat_1 @ sk_C_2 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(d18_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (v4_relat_1 @ X11 @ X12)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.50          | (v1_relat_1 @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('17', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '17'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_2))
% 0.20/0.50        | (r2_hidden @ (sk_C_1 @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '20'])).
% 0.20/0.50  thf(t1_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_2))
% 0.20/0.50        | (m1_subset_1 @ (sk_C_1 @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_xboole_0) = (X0))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X27 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_2))
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k1_relset_1 @ sk_B @ sk_A @ sk_C_2))
% 0.20/0.50        | ~ (m1_subset_1 @ 
% 0.20/0.50             (sk_C_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_2) @ k1_xboole_0) @ 
% 0.20/0.50             sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.50         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_2))
% 0.20/0.50        | ~ (m1_subset_1 @ (sk_C_1 @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0) @ 
% 0.20/0.50             sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '29', '30'])).
% 0.20/0.50  thf('32', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.50      inference('clc', [status(thm)], ['23', '31'])).
% 0.20/0.50  thf(t65_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X15 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.20/0.50          | ((k2_relat_1 @ X15) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_C_2)
% 0.20/0.50        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.50  thf('38', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '37'])).
% 0.20/0.50  thf('39', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
