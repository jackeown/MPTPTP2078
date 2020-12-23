%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9McFcLsWZG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:04 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  396 ( 819 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('1',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X27 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('11',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['13','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['7','24'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('29',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X14: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9McFcLsWZG
% 0.13/0.37  % Computer   : n020.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 11:11:22 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 78 iterations in 0.041s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.23/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.53  thf(d1_xboole_0, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.53  thf('0', plain,
% 0.23/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.53  thf(t49_relset_1, conjecture,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.53           ( ![C:$i]:
% 0.23/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.23/0.53                    ( ![D:$i]:
% 0.23/0.53                      ( ( m1_subset_1 @ D @ B ) =>
% 0.23/0.53                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i]:
% 0.23/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.53          ( ![B:$i]:
% 0.23/0.53            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.53              ( ![C:$i]:
% 0.23/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.23/0.53                       ( ![D:$i]:
% 0.23/0.53                         ( ( m1_subset_1 @ D @ B ) =>
% 0.23/0.53                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.23/0.53  thf('1', plain,
% 0.23/0.53      (![X27 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X27 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.23/0.53          | ~ (m1_subset_1 @ X27 @ sk_B_1))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (((v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.23/0.53        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.23/0.53             sk_B_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.53         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.23/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.53  thf('7', plain,
% 0.23/0.53      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.23/0.53        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.23/0.53      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.53  thf('9', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc2_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.53  thf('10', plain,
% 0.23/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.53         ((v5_relat_1 @ X18 @ X20)
% 0.23/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.53  thf('11', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.23/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.53  thf(d19_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ B ) =>
% 0.23/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.53  thf('12', plain,
% 0.23/0.53      (![X12 : $i, X13 : $i]:
% 0.23/0.53         (~ (v5_relat_1 @ X12 @ X13)
% 0.23/0.53          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.23/0.53          | ~ (v1_relat_1 @ X12))),
% 0.23/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.53  thf('14', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc2_relat_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.53  thf('15', plain,
% 0.23/0.53      (![X10 : $i, X11 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.23/0.53          | (v1_relat_1 @ X10)
% 0.23/0.53          | ~ (v1_relat_1 @ X11))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.53  thf(fc6_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.53  thf('17', plain,
% 0.23/0.53      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.53  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.23/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.53  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.23/0.53      inference('demod', [status(thm)], ['13', '18'])).
% 0.23/0.53  thf(d3_tarski, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.53  thf('20', plain,
% 0.23/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.23/0.53          | (r2_hidden @ X3 @ X5)
% 0.23/0.53          | ~ (r1_tarski @ X4 @ X5))),
% 0.23/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((r2_hidden @ X0 @ sk_B_1)
% 0.23/0.53          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.23/0.53        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['8', '21'])).
% 0.23/0.53  thf(t1_subset, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.23/0.53  thf('23', plain,
% 0.23/0.53      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.23/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.23/0.53  thf('24', plain,
% 0.23/0.53      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.23/0.53        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.53  thf('25', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.23/0.53      inference('clc', [status(thm)], ['7', '24'])).
% 0.23/0.53  thf(fc9_relat_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.23/0.53       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      (![X17 : $i]:
% 0.23/0.53         (~ (v1_xboole_0 @ (k2_relat_1 @ X17))
% 0.23/0.53          | ~ (v1_relat_1 @ X17)
% 0.23/0.53          | (v1_xboole_0 @ X17))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.23/0.53  thf('27', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_relat_1 @ sk_C_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.53  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.23/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.53  thf('29', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.23/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.53  thf(fc10_relat_1, axiom,
% 0.23/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      (![X14 : $i]:
% 0.23/0.53         ((v1_xboole_0 @ (k1_relat_1 @ X14)) | ~ (v1_xboole_0 @ X14))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.23/0.53  thf(l13_xboole_0, axiom,
% 0.23/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.53  thf('31', plain,
% 0.23/0.53      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.23/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.23/0.53  thf('32', plain,
% 0.23/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.53  thf('33', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['29', '32'])).
% 0.23/0.53  thf('34', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('35', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.53  thf('36', plain,
% 0.23/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.53         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.23/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.53  thf('37', plain,
% 0.23/0.53      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.23/0.53  thf('38', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['34', '37'])).
% 0.23/0.53  thf('39', plain, ($false),
% 0.23/0.53      inference('simplify_reflect-', [status(thm)], ['33', '38'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
