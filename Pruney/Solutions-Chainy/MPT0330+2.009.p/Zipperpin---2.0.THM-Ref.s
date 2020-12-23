%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WRYQdun09I

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:00 EST 2020

% Result     : Theorem 56.90s
% Output     : Refutation 56.90s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  357 ( 569 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t143_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
        & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
          & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ X28 @ ( k2_xboole_0 @ X25 @ X27 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X25 ) @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X2 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ sk_C ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('27',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WRYQdun09I
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 56.90/57.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 56.90/57.14  % Solved by: fo/fo7.sh
% 56.90/57.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.90/57.14  % done 36974 iterations in 56.676s
% 56.90/57.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 56.90/57.14  % SZS output start Refutation
% 56.90/57.14  thf(sk_F_type, type, sk_F: $i).
% 56.90/57.14  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 56.90/57.14  thf(sk_A_type, type, sk_A: $i).
% 56.90/57.14  thf(sk_C_type, type, sk_C: $i).
% 56.90/57.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 56.90/57.14  thf(sk_E_type, type, sk_E: $i).
% 56.90/57.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 56.90/57.14  thf(sk_B_type, type, sk_B: $i).
% 56.90/57.14  thf(sk_D_type, type, sk_D: $i).
% 56.90/57.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 56.90/57.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 56.90/57.14  thf(t143_zfmisc_1, conjecture,
% 56.90/57.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 56.90/57.14     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 56.90/57.14         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 56.90/57.14       ( r1_tarski @
% 56.90/57.14         ( k2_xboole_0 @ A @ B ) @ 
% 56.90/57.14         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 56.90/57.14  thf(zf_stmt_0, negated_conjecture,
% 56.90/57.14    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 56.90/57.14        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 56.90/57.14            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 56.90/57.14          ( r1_tarski @
% 56.90/57.14            ( k2_xboole_0 @ A @ B ) @ 
% 56.90/57.14            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 56.90/57.14    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 56.90/57.14  thf('0', plain,
% 56.90/57.14      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 56.90/57.14          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 56.90/57.14           (k2_xboole_0 @ sk_D @ sk_F)))),
% 56.90/57.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.90/57.14  thf(t120_zfmisc_1, axiom,
% 56.90/57.14    (![A:$i,B:$i,C:$i]:
% 56.90/57.14     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 56.90/57.14         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 56.90/57.14       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 56.90/57.14         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 56.90/57.14  thf('1', plain,
% 56.90/57.14      (![X25 : $i, X27 : $i, X28 : $i]:
% 56.90/57.14         ((k2_zfmisc_1 @ X28 @ (k2_xboole_0 @ X25 @ X27))
% 56.90/57.14           = (k2_xboole_0 @ (k2_zfmisc_1 @ X28 @ X25) @ 
% 56.90/57.14              (k2_zfmisc_1 @ X28 @ X27)))),
% 56.90/57.14      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 56.90/57.14  thf('2', plain,
% 56.90/57.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 56.90/57.14         ((k2_zfmisc_1 @ (k2_xboole_0 @ X25 @ X27) @ X26)
% 56.90/57.14           = (k2_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 56.90/57.14              (k2_zfmisc_1 @ X27 @ X26)))),
% 56.90/57.14      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 56.90/57.14  thf(t7_xboole_1, axiom,
% 56.90/57.14    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 56.90/57.14  thf('3', plain,
% 56.90/57.14      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 56.90/57.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 56.90/57.14  thf('4', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 56.90/57.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.90/57.14  thf(t1_xboole_1, axiom,
% 56.90/57.14    (![A:$i,B:$i,C:$i]:
% 56.90/57.14     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 56.90/57.14       ( r1_tarski @ A @ C ) ))).
% 56.90/57.14  thf('5', plain,
% 56.90/57.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 56.90/57.14         (~ (r1_tarski @ X8 @ X9)
% 56.90/57.14          | ~ (r1_tarski @ X9 @ X10)
% 56.90/57.14          | (r1_tarski @ X8 @ X10))),
% 56.90/57.14      inference('cnf', [status(esa)], [t1_xboole_1])).
% 56.90/57.14  thf('6', plain,
% 56.90/57.14      (![X0 : $i]:
% 56.90/57.14         ((r1_tarski @ sk_B @ X0)
% 56.90/57.14          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 56.90/57.14      inference('sup-', [status(thm)], ['4', '5'])).
% 56.90/57.14  thf('7', plain,
% 56.90/57.14      (![X0 : $i]:
% 56.90/57.14         (r1_tarski @ sk_B @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 56.90/57.14      inference('sup-', [status(thm)], ['3', '6'])).
% 56.90/57.14  thf('8', plain,
% 56.90/57.14      (![X0 : $i]:
% 56.90/57.14         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F))),
% 56.90/57.14      inference('sup+', [status(thm)], ['2', '7'])).
% 56.90/57.14  thf('9', plain,
% 56.90/57.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 56.90/57.14         ((k2_zfmisc_1 @ (k2_xboole_0 @ X25 @ X27) @ X26)
% 56.90/57.14           = (k2_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 56.90/57.14              (k2_zfmisc_1 @ X27 @ X26)))),
% 56.90/57.14      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 56.90/57.14  thf(commutativity_k2_tarski, axiom,
% 56.90/57.14    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 56.90/57.14  thf('10', plain,
% 56.90/57.14      (![X19 : $i, X20 : $i]:
% 56.90/57.14         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 56.90/57.14      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 56.90/57.14  thf(l51_zfmisc_1, axiom,
% 56.90/57.14    (![A:$i,B:$i]:
% 56.90/57.14     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 56.90/57.14  thf('11', plain,
% 56.90/57.14      (![X23 : $i, X24 : $i]:
% 56.90/57.14         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 56.90/57.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 56.90/57.14  thf('12', plain,
% 56.90/57.14      (![X0 : $i, X1 : $i]:
% 56.90/57.14         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 56.90/57.14      inference('sup+', [status(thm)], ['10', '11'])).
% 56.90/57.14  thf('13', plain,
% 56.90/57.14      (![X23 : $i, X24 : $i]:
% 56.90/57.14         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 56.90/57.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 56.90/57.14  thf('14', plain,
% 56.90/57.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.90/57.14      inference('sup+', [status(thm)], ['12', '13'])).
% 56.90/57.14  thf('15', plain,
% 56.90/57.14      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 56.90/57.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 56.90/57.14  thf('16', plain,
% 56.90/57.14      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 56.90/57.14      inference('sup+', [status(thm)], ['14', '15'])).
% 56.90/57.14  thf('17', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 56.90/57.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.90/57.14  thf('18', plain,
% 56.90/57.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 56.90/57.14         (~ (r1_tarski @ X8 @ X9)
% 56.90/57.14          | ~ (r1_tarski @ X9 @ X10)
% 56.90/57.14          | (r1_tarski @ X8 @ X10))),
% 56.90/57.14      inference('cnf', [status(esa)], [t1_xboole_1])).
% 56.90/57.14  thf('19', plain,
% 56.90/57.14      (![X0 : $i]:
% 56.90/57.14         ((r1_tarski @ sk_A @ X0)
% 56.90/57.14          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 56.90/57.14      inference('sup-', [status(thm)], ['17', '18'])).
% 56.90/57.14  thf('20', plain,
% 56.90/57.14      (![X0 : $i]:
% 56.90/57.14         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 56.90/57.14      inference('sup-', [status(thm)], ['16', '19'])).
% 56.90/57.14  thf('21', plain,
% 56.90/57.14      (![X0 : $i]:
% 56.90/57.14         (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 56.90/57.14      inference('sup+', [status(thm)], ['9', '20'])).
% 56.90/57.14  thf(t13_xboole_1, axiom,
% 56.90/57.14    (![A:$i,B:$i,C:$i,D:$i]:
% 56.90/57.14     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 56.90/57.14       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 56.90/57.14  thf('22', plain,
% 56.90/57.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 56.90/57.14         (~ (r1_tarski @ X4 @ X5)
% 56.90/57.14          | ~ (r1_tarski @ X6 @ X7)
% 56.90/57.14          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ (k2_xboole_0 @ X5 @ X7)))),
% 56.90/57.14      inference('cnf', [status(esa)], [t13_xboole_1])).
% 56.90/57.14  thf('23', plain,
% 56.90/57.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.90/57.14         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X2) @ 
% 56.90/57.14           (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D) @ X1))
% 56.90/57.14          | ~ (r1_tarski @ X2 @ X1))),
% 56.90/57.14      inference('sup-', [status(thm)], ['21', '22'])).
% 56.90/57.14  thf('24', plain,
% 56.90/57.14      (![X0 : $i, X1 : $i]:
% 56.90/57.14         (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 56.90/57.14          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C) @ sk_D) @ 
% 56.90/57.14           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F)))),
% 56.90/57.14      inference('sup-', [status(thm)], ['8', '23'])).
% 56.90/57.14  thf('25', plain,
% 56.90/57.14      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 56.90/57.14        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ sk_C) @ 
% 56.90/57.14         (k2_xboole_0 @ sk_D @ sk_F)))),
% 56.90/57.14      inference('sup+', [status(thm)], ['1', '24'])).
% 56.90/57.14  thf('26', plain,
% 56.90/57.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.90/57.14      inference('sup+', [status(thm)], ['12', '13'])).
% 56.90/57.14  thf('27', plain,
% 56.90/57.14      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 56.90/57.14        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 56.90/57.14         (k2_xboole_0 @ sk_D @ sk_F)))),
% 56.90/57.14      inference('demod', [status(thm)], ['25', '26'])).
% 56.90/57.14  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 56.90/57.14  
% 56.90/57.14  % SZS output end Refutation
% 56.90/57.14  
% 56.90/57.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
