%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zgDryOslZ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   72 (  80 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  426 ( 493 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('3',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_A )
      | ~ ( r1_xboole_0 @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_hidden @ X19 @ ( sk_C_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['4','11'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ( m1_subset_1 @ X22 @ X21 )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( r2_hidden @ X29 @ X27 )
      | ( r2_hidden @ X29 @ ( k3_subset_1 @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zgDryOslZ
% 0.16/0.37  % Computer   : n006.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:54:38 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 224 iterations in 0.059s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.23/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(d1_xboole_0, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.52  thf(t7_tarski, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ~( ( r2_hidden @ A @ B ) & 
% 0.23/0.52          ( ![C:$i]:
% 0.23/0.52            ( ~( ( r2_hidden @ C @ B ) & 
% 0.23/0.52                 ( ![D:$i]:
% 0.23/0.52                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (![X17 : $i, X18 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X17 @ X18) | (r2_hidden @ (sk_C_1 @ X18) @ X18))),
% 0.23/0.52      inference('cnf', [status(esa)], [t7_tarski])).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.52  thf(t1_mcart_1, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.52          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.52             ( ![B:$i]:
% 0.23/0.52               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      (![X37 : $i]: (~ (r2_hidden @ X37 @ sk_A) | ~ (r1_xboole_0 @ X37 @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (((v1_xboole_0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.52  thf(t3_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (![X3 : $i, X4 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.23/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      (![X3 : $i, X4 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.23/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X17 @ X18)
% 0.23/0.52          | ~ (r2_hidden @ X19 @ X18)
% 0.23/0.52          | ~ (r2_hidden @ X19 @ (sk_C_1 @ X18)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t7_tarski])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.23/0.52      inference('condensation', [status(thm)], ['7'])).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.23/0.52          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['6', '8'])).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.23/0.52          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['5', '9'])).
% 0.23/0.52  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.23/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.52  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 0.23/0.52      inference('demod', [status(thm)], ['4', '11'])).
% 0.23/0.52  thf(d2_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i]:
% 0.23/0.52         (~ (v1_xboole_0 @ X22)
% 0.23/0.52          | (m1_subset_1 @ X22 @ X21)
% 0.23/0.52          | ~ (v1_xboole_0 @ X21))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.52  thf(t4_subset_1, axiom,
% 0.23/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X26 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.23/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.52  thf(t50_subset_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.23/0.52               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.23/0.52                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.23/0.52          | (r2_hidden @ X29 @ X27)
% 0.23/0.52          | (r2_hidden @ X29 @ (k3_subset_1 @ X28 @ X27))
% 0.23/0.52          | ~ (m1_subset_1 @ X29 @ X28)
% 0.23/0.52          | ((X28) = (k1_xboole_0)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((X0) = (k1_xboole_0))
% 0.23/0.52          | ~ (m1_subset_1 @ X1 @ X0)
% 0.23/0.52          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.23/0.52          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      (![X26 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.23/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.52  thf(d5_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i]:
% 0.23/0.52         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.23/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.52  thf(t2_boole, axiom,
% 0.23/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.23/0.52  thf(t100_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (![X7 : $i, X8 : $i]:
% 0.23/0.52         ((k4_xboole_0 @ X7 @ X8)
% 0.23/0.52           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.23/0.52  thf(t5_boole, axiom,
% 0.23/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.52  thf('23', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.23/0.52  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.23/0.52  thf('25', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.52      inference('demod', [status(thm)], ['19', '24'])).
% 0.23/0.52  thf('26', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((X0) = (k1_xboole_0))
% 0.23/0.52          | ~ (m1_subset_1 @ X1 @ X0)
% 0.23/0.52          | (r2_hidden @ X1 @ X0)
% 0.23/0.52          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['16', '25'])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (v1_xboole_0 @ X0)
% 0.23/0.52          | ~ (v1_xboole_0 @ X1)
% 0.23/0.52          | (r2_hidden @ X1 @ k1_xboole_0)
% 0.23/0.52          | (r2_hidden @ X1 @ X0)
% 0.23/0.52          | ((X0) = (k1_xboole_0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['13', '26'])).
% 0.23/0.52  thf('28', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.52  thf('29', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((X1) = (k1_xboole_0))
% 0.23/0.52          | (r2_hidden @ X0 @ X1)
% 0.23/0.52          | ~ (v1_xboole_0 @ X0)
% 0.23/0.52          | ~ (v1_xboole_0 @ X1)
% 0.23/0.52          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.52  thf('30', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.23/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.52  thf(t7_ordinal1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      (![X35 : $i, X36 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.23/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.23/0.52  thf('33', plain,
% 0.23/0.52      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.52  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.52      inference('sup-', [status(thm)], ['30', '33'])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((X1) = (k1_xboole_0))
% 0.23/0.52          | (r2_hidden @ X0 @ X1)
% 0.23/0.52          | ~ (v1_xboole_0 @ X0)
% 0.23/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.23/0.52      inference('demod', [status(thm)], ['29', '34'])).
% 0.23/0.52  thf('36', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.52  thf('37', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (v1_xboole_0 @ X0)
% 0.23/0.52          | ~ (v1_xboole_0 @ X1)
% 0.23/0.52          | ((X0) = (k1_xboole_0))
% 0.23/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.23/0.52  thf('39', plain,
% 0.23/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.52      inference('condensation', [status(thm)], ['38'])).
% 0.23/0.52  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['12', '39'])).
% 0.23/0.52  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('42', plain, ($false),
% 0.23/0.52      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
