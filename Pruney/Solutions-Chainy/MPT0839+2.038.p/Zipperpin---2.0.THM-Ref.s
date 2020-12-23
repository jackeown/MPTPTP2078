%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7XVCUZ5MLC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 (  88 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  400 ( 736 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X30 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X30 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('11',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['13','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X30: $i] :
      ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['8','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','34'])).

thf('36',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7XVCUZ5MLC
% 0.13/0.32  % Computer   : n001.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:47:15 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 87 iterations in 0.034s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(t50_relset_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.47               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47                    ( ![D:$i]:
% 0.19/0.47                      ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.47                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.47                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47                       ( ![D:$i]:
% 0.19/0.47                         ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.47                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.47         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.19/0.47          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.47  thf(d3_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X1 : $i, X3 : $i]:
% 0.19/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X30 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X30 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.19/0.47          | ~ (m1_subset_1 @ X30 @ sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.47         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.19/0.47          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X30 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X30 @ (k1_relat_1 @ sk_C_1))
% 0.19/0.47          | ~ (m1_subset_1 @ X30 @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['4', '7'])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc2_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.47         ((v4_relat_1 @ X21 @ X22)
% 0.19/0.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.47  thf('11', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.19/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf(d18_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ B ) =>
% 0.19/0.47       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X16 : $i, X17 : $i]:
% 0.19/0.47         (~ (v4_relat_1 @ X16 @ X17)
% 0.19/0.47          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.19/0.47          | ~ (v1_relat_1 @ X16))),
% 0.19/0.47      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc2_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.19/0.47          | (v1_relat_1 @ X14)
% 0.19/0.47          | ~ (v1_relat_1 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf(fc6_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.47  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.19/0.47      inference('demod', [status(thm)], ['13', '18'])).
% 0.19/0.47  thf(t3_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X8 : $i, X10 : $i]:
% 0.19/0.47         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.47  thf(t4_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.19/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X11 @ X12)
% 0.19/0.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.19/0.47          | (m1_subset_1 @ X11 @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((m1_subset_1 @ X0 @ sk_B)
% 0.19/0.47          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.47  thf('24', plain, (![X30 : $i]: ~ (r2_hidden @ X30 @ (k1_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('clc', [status(thm)], ['8', '23'])).
% 0.19/0.47  thf('25', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '24'])).
% 0.19/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.47  thf('26', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.47  thf(d10_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.47  thf('27', plain,
% 0.19/0.47      (![X4 : $i, X6 : $i]:
% 0.19/0.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.47  thf('29', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['25', '28'])).
% 0.19/0.47  thf(t65_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.47         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (![X20 : $i]:
% 0.19/0.47         (((k1_relat_1 @ X20) != (k1_xboole_0))
% 0.19/0.47          | ((k2_relat_1 @ X20) = (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ X20))),
% 0.19/0.47      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.47        | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.47        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.47  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.47        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.47  thf('34', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.47  thf('35', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['2', '34'])).
% 0.19/0.47  thf('36', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('37', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
