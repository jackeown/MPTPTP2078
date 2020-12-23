%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.76pd42ozOt

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:27 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 293 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  554 (4537 expanded)
%              Number of equality atoms :   30 ( 262 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( sk_B
      = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('13',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X15 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( sk_B = X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) ) @ sk_A )
    | ( sk_B
      = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X15 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( sk_E @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X11 ) @ ( k2_relset_1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) ) ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('29',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_B )
      | ( X15
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B )
    = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['11','37','38','39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.76pd42ozOt
% 0.17/0.37  % Computer   : n005.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:40:18 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 156 iterations in 0.092s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(sk_E_type, type, sk_E: $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(t2_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.39/0.58       ( ( A ) = ( B ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((X1) = (X0))
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_tarski])).
% 0.39/0.58  thf(t16_funct_2, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58       ( ( ![D:$i]:
% 0.39/0.58           ( ~( ( r2_hidden @ D @ B ) & 
% 0.39/0.58                ( ![E:$i]:
% 0.39/0.58                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.39/0.58                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.39/0.58         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58          ( ( ![D:$i]:
% 0.39/0.58              ( ~( ( r2_hidden @ D @ B ) & 
% 0.39/0.58                   ( ![E:$i]:
% 0.39/0.58                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.39/0.58                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.39/0.58            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(dt_k2_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (k2_relset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.39/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.39/0.58        (k1_zfmisc_1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf(l3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.58          | (r2_hidden @ X3 @ X5)
% 0.39/0.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ sk_B)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ X0) @ X0)
% 0.39/0.58          | ((X0) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.39/0.58          | (r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ X0) @ 
% 0.39/0.58             sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      ((((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.39/0.58        | (r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ 
% 0.39/0.58           sk_B))),
% 0.39/0.58      inference('eq_fact', [status(thm)], ['6'])).
% 0.39/0.58  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      ((r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ sk_B)),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf(t7_ordinal1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]: (~ (r2_hidden @ X6 @ X7) | ~ (r1_tarski @ X7 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (~ (r1_tarski @ sk_B @ 
% 0.39/0.58          (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((X1) = (X0))
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_tarski])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X15 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X15 @ sk_B) | (r2_hidden @ (sk_E @ X15) @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ X0)
% 0.39/0.58          | ((sk_B) = (X0))
% 0.39/0.58          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ sk_B)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (((r2_hidden @ 
% 0.39/0.58         (sk_E @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B)) @ sk_A)
% 0.39/0.58        | ((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.39/0.58        | (r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ 
% 0.39/0.58           sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('17', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (((r2_hidden @ 
% 0.39/0.58         (sk_E @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B)) @ sk_A)
% 0.39/0.58        | (r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ 
% 0.39/0.58           sk_B))),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X15 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X15 @ sk_B) | (r2_hidden @ (sk_E @ X15) @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      ((r2_hidden @ 
% 0.39/0.58        (sk_E @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B)) @ sk_A)),
% 0.39/0.58      inference('clc', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t6_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58       ( ( r2_hidden @ C @ A ) =>
% 0.39/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.58           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.39/0.58          | ((X13) = (k1_xboole_0))
% 0.39/0.58          | ~ (v1_funct_1 @ X14)
% 0.39/0.58          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.39/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.39/0.58          | (r2_hidden @ (k1_funct_1 @ X14 @ X11) @ 
% 0.39/0.58             (k2_relset_1 @ X12 @ X13 @ X14)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.39/0.58           (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.39/0.58          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_C_1)
% 0.39/0.58          | ((sk_B) = (k1_xboole_0))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf('24', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('25', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.39/0.58           (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.39/0.58          | ((sk_B) = (k1_xboole_0))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      ((((sk_B) = (k1_xboole_0))
% 0.39/0.58        | (r2_hidden @ 
% 0.39/0.58           (k1_funct_1 @ sk_C_1 @ 
% 0.39/0.58            (sk_E @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B))) @ 
% 0.39/0.58           (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ sk_B)),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X15 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X15 @ sk_B)
% 0.39/0.58          | ((X15) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X15))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (((sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B)
% 0.39/0.58         = (k1_funct_1 @ sk_C_1 @ 
% 0.39/0.58            (sk_E @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((((sk_B) = (k1_xboole_0))
% 0.39/0.58        | (r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ 
% 0.39/0.58           (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('demod', [status(thm)], ['27', '30'])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((X1) = (X0))
% 0.39/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.39/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_tarski])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      ((((sk_B) = (k1_xboole_0))
% 0.39/0.58        | ~ (r2_hidden @ 
% 0.39/0.58             (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ sk_B)
% 0.39/0.58        | ((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      ((r2_hidden @ (sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_B) @ sk_B)),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((((sk_B) = (k1_xboole_0))
% 0.39/0.58        | ((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('37', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('38', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('39', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.58  thf('40', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf('41', plain, ($false),
% 0.39/0.58      inference('demod', [status(thm)], ['11', '37', '38', '39', '40'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
