%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gm1847ZxCG

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:33 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 101 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  438 ( 848 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t158_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k9_relat_1 @ X26 @ X27 ) @ ( k9_relat_1 @ X25 @ X27 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( ( ( k9_relat_1 @ X21 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('11',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t155_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ X22 @ X23 ) @ ( k9_relat_1 @ X22 @ X24 ) ) @ ( k9_relat_1 @ X22 @ ( k6_subset_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t155_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X22 @ X23 ) @ ( k9_relat_1 @ X22 @ X24 ) ) @ ( k9_relat_1 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['8','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gm1847ZxCG
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:19:09 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 3.86/4.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.86/4.03  % Solved by: fo/fo7.sh
% 3.86/4.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.86/4.03  % done 7107 iterations in 3.557s
% 3.86/4.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.86/4.03  % SZS output start Refutation
% 3.86/4.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.86/4.03  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.86/4.03  thf(sk_C_type, type, sk_C: $i).
% 3.86/4.03  thf(sk_D_type, type, sk_D: $i).
% 3.86/4.03  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.86/4.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.86/4.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.86/4.03  thf(sk_B_type, type, sk_B: $i).
% 3.86/4.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.86/4.03  thf(sk_A_type, type, sk_A: $i).
% 3.86/4.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.86/4.03  thf(t158_relat_1, conjecture,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( v1_relat_1 @ C ) =>
% 3.86/4.03       ( ![D:$i]:
% 3.86/4.03         ( ( v1_relat_1 @ D ) =>
% 3.86/4.03           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 3.86/4.03             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 3.86/4.03  thf(zf_stmt_0, negated_conjecture,
% 3.86/4.03    (~( ![A:$i,B:$i,C:$i]:
% 3.86/4.03        ( ( v1_relat_1 @ C ) =>
% 3.86/4.03          ( ![D:$i]:
% 3.86/4.03            ( ( v1_relat_1 @ D ) =>
% 3.86/4.03              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 3.86/4.03                ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ) )),
% 3.86/4.03    inference('cnf.neg', [status(esa)], [t158_relat_1])).
% 3.86/4.03  thf('0', plain,
% 3.86/4.03      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf(t157_relat_1, axiom,
% 3.86/4.03    (![A:$i,B:$i]:
% 3.86/4.03     ( ( v1_relat_1 @ B ) =>
% 3.86/4.03       ( ![C:$i]:
% 3.86/4.03         ( ( v1_relat_1 @ C ) =>
% 3.86/4.03           ( ( r1_tarski @ B @ C ) =>
% 3.86/4.03             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 3.86/4.03  thf('2', plain,
% 3.86/4.03      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.86/4.03         (~ (v1_relat_1 @ X25)
% 3.86/4.03          | (r1_tarski @ (k9_relat_1 @ X26 @ X27) @ (k9_relat_1 @ X25 @ X27))
% 3.86/4.03          | ~ (r1_tarski @ X26 @ X25)
% 3.86/4.03          | ~ (v1_relat_1 @ X26))),
% 3.86/4.03      inference('cnf', [status(esa)], [t157_relat_1])).
% 3.86/4.03  thf('3', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (~ (v1_relat_1 @ sk_C)
% 3.86/4.03          | (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))
% 3.86/4.03          | ~ (v1_relat_1 @ sk_D))),
% 3.86/4.03      inference('sup-', [status(thm)], ['1', '2'])).
% 3.86/4.03  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('5', plain, ((v1_relat_1 @ sk_D)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('6', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))),
% 3.86/4.03      inference('demod', [status(thm)], ['3', '4', '5'])).
% 3.86/4.03  thf(t12_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i]:
% 3.86/4.03     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.86/4.03  thf('7', plain,
% 3.86/4.03      (![X8 : $i, X9 : $i]:
% 3.86/4.03         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 3.86/4.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.86/4.03  thf('8', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         ((k2_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))
% 3.86/4.03           = (k9_relat_1 @ sk_D @ X0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['6', '7'])).
% 3.86/4.03  thf(t149_relat_1, axiom,
% 3.86/4.03    (![A:$i]:
% 3.86/4.03     ( ( v1_relat_1 @ A ) =>
% 3.86/4.03       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 3.86/4.03  thf('9', plain,
% 3.86/4.03      (![X21 : $i]:
% 3.86/4.03         (((k9_relat_1 @ X21 @ k1_xboole_0) = (k1_xboole_0))
% 3.86/4.03          | ~ (v1_relat_1 @ X21))),
% 3.86/4.03      inference('cnf', [status(esa)], [t149_relat_1])).
% 3.86/4.03  thf('10', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))),
% 3.86/4.03      inference('demod', [status(thm)], ['3', '4', '5'])).
% 3.86/4.03  thf('11', plain,
% 3.86/4.03      (((r1_tarski @ (k9_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)
% 3.86/4.03        | ~ (v1_relat_1 @ sk_D))),
% 3.86/4.03      inference('sup+', [status(thm)], ['9', '10'])).
% 3.86/4.03  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('13', plain,
% 3.86/4.03      ((r1_tarski @ (k9_relat_1 @ sk_C @ k1_xboole_0) @ k1_xboole_0)),
% 3.86/4.03      inference('demod', [status(thm)], ['11', '12'])).
% 3.86/4.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.86/4.03  thf('14', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 3.86/4.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.86/4.03  thf(d10_xboole_0, axiom,
% 3.86/4.03    (![A:$i,B:$i]:
% 3.86/4.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.86/4.03  thf('15', plain,
% 3.86/4.03      (![X2 : $i, X4 : $i]:
% 3.86/4.03         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.86/4.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.86/4.03  thf('16', plain,
% 3.86/4.03      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['14', '15'])).
% 3.86/4.03  thf('17', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['13', '16'])).
% 3.86/4.03  thf(commutativity_k2_xboole_0, axiom,
% 3.86/4.03    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.86/4.03  thf('18', plain,
% 3.86/4.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.86/4.03      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.86/4.03  thf('19', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf(t10_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.86/4.03  thf('20', plain,
% 3.86/4.03      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.86/4.03         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 3.86/4.03      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.86/4.03  thf('21', plain,
% 3.86/4.03      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))),
% 3.86/4.03      inference('sup-', [status(thm)], ['19', '20'])).
% 3.86/4.03  thf('22', plain,
% 3.86/4.03      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 3.86/4.03      inference('sup+', [status(thm)], ['18', '21'])).
% 3.86/4.03  thf(t43_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.86/4.03       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.86/4.03  thf('23', plain,
% 3.86/4.03      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.86/4.03         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 3.86/4.03          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.86/4.03      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.86/4.03  thf('24', plain,
% 3.86/4.03      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 3.86/4.03      inference('sup-', [status(thm)], ['22', '23'])).
% 3.86/4.03  thf('25', plain,
% 3.86/4.03      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['14', '15'])).
% 3.86/4.03  thf('26', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['24', '25'])).
% 3.86/4.03  thf(t155_relat_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( v1_relat_1 @ C ) =>
% 3.86/4.03       ( r1_tarski @
% 3.86/4.03         ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 3.86/4.03         ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ))).
% 3.86/4.03  thf('27', plain,
% 3.86/4.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.86/4.03         ((r1_tarski @ 
% 3.86/4.03           (k6_subset_1 @ (k9_relat_1 @ X22 @ X23) @ (k9_relat_1 @ X22 @ X24)) @ 
% 3.86/4.03           (k9_relat_1 @ X22 @ (k6_subset_1 @ X23 @ X24)))
% 3.86/4.03          | ~ (v1_relat_1 @ X22))),
% 3.86/4.03      inference('cnf', [status(esa)], [t155_relat_1])).
% 3.86/4.03  thf(redefinition_k6_subset_1, axiom,
% 3.86/4.03    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.86/4.03  thf('28', plain,
% 3.86/4.03      (![X19 : $i, X20 : $i]:
% 3.86/4.03         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 3.86/4.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.86/4.03  thf('29', plain,
% 3.86/4.03      (![X19 : $i, X20 : $i]:
% 3.86/4.03         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 3.86/4.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.86/4.03  thf('30', plain,
% 3.86/4.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.86/4.03         ((r1_tarski @ 
% 3.86/4.03           (k4_xboole_0 @ (k9_relat_1 @ X22 @ X23) @ (k9_relat_1 @ X22 @ X24)) @ 
% 3.86/4.03           (k9_relat_1 @ X22 @ (k4_xboole_0 @ X23 @ X24)))
% 3.86/4.03          | ~ (v1_relat_1 @ X22))),
% 3.86/4.03      inference('demod', [status(thm)], ['27', '28', '29'])).
% 3.86/4.03  thf('31', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         ((r1_tarski @ 
% 3.86/4.03           (k4_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)) @ 
% 3.86/4.03           (k9_relat_1 @ X0 @ k1_xboole_0))
% 3.86/4.03          | ~ (v1_relat_1 @ X0))),
% 3.86/4.03      inference('sup+', [status(thm)], ['26', '30'])).
% 3.86/4.03  thf('32', plain,
% 3.86/4.03      (((r1_tarski @ 
% 3.86/4.03         (k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B)) @ 
% 3.86/4.03         k1_xboole_0)
% 3.86/4.03        | ~ (v1_relat_1 @ sk_C))),
% 3.86/4.03      inference('sup+', [status(thm)], ['17', '31'])).
% 3.86/4.03  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('34', plain,
% 3.86/4.03      ((r1_tarski @ 
% 3.86/4.03        (k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B)) @ 
% 3.86/4.03        k1_xboole_0)),
% 3.86/4.03      inference('demod', [status(thm)], ['32', '33'])).
% 3.86/4.03  thf('35', plain,
% 3.86/4.03      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['14', '15'])).
% 3.86/4.03  thf('36', plain,
% 3.86/4.03      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 3.86/4.03         = (k1_xboole_0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['34', '35'])).
% 3.86/4.03  thf(t44_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.86/4.03       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.86/4.03  thf('37', plain,
% 3.86/4.03      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.86/4.03         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 3.86/4.03          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 3.86/4.03      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.86/4.03  thf('38', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.86/4.03          | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 3.86/4.03             (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_B) @ X0)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['36', '37'])).
% 3.86/4.03  thf('39', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 3.86/4.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.86/4.03  thf('40', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 3.86/4.03          (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_B) @ X0))),
% 3.86/4.03      inference('demod', [status(thm)], ['38', '39'])).
% 3.86/4.03  thf('41', plain,
% 3.86/4.03      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))),
% 3.86/4.03      inference('sup+', [status(thm)], ['8', '40'])).
% 3.86/4.03  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 3.86/4.03  
% 3.86/4.03  % SZS output end Refutation
% 3.86/4.03  
% 3.86/4.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
