%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ld825L7NeU

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 (  91 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  383 ( 454 expanded)
%              Number of equality atoms :   41 (  53 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('0',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X34: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X48: $i] :
      ( ( k9_setfam_1 @ X48 )
      = ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X34: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X34 ) )
      = X34 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X49: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X50: $i] :
      ( ( k3_yellow_1 @ X50 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('9',plain,(
    ! [X34: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X34 ) )
      = X34 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('12',plain,(
    ! [X48: $i] :
      ( ( k9_setfam_1 @ X48 )
      = ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('15',plain,(
    ! [X48: $i] :
      ( ( k9_setfam_1 @ X48 )
      = ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X48: $i] :
      ( ( k9_setfam_1 @ X48 )
      = ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('17',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X37 @ X38 ) @ ( k9_setfam_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k9_setfam_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,(
    ! [X48: $i] :
      ( ( k9_setfam_1 @ X48 )
      = ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('22',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k9_setfam_1 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','33'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ X43 @ X44 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('37',plain,(
    ! [X39: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('38',plain,(
    ! [X48: $i] :
      ( ( k9_setfam_1 @ X48 )
      = ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('39',plain,(
    ! [X39: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','40'])).

thf('42',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ld825L7NeU
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:42:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 47 iterations in 0.018s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.19/0.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.46  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(t19_yellow_1, conjecture,
% 0.19/0.46    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.19/0.46  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t99_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.19/0.46  thf('1', plain, (![X34 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X34)) = (X34))),
% 0.19/0.46      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.19/0.46  thf(redefinition_k9_setfam_1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.46  thf('2', plain, (![X48 : $i]: ((k9_setfam_1 @ X48) = (k1_zfmisc_1 @ X48))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('3', plain, (![X34 : $i]: ((k3_tarski @ (k9_setfam_1 @ X34)) = (X34))),
% 0.19/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t14_yellow_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.46       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.19/0.46         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X49 : $i]:
% 0.19/0.46         (~ (r2_hidden @ (k3_tarski @ X49) @ X49)
% 0.19/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 0.19/0.46          | (v1_xboole_0 @ X49))),
% 0.19/0.46      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.19/0.46  thf(d1_xboole_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X49 : $i]:
% 0.19/0.46         (((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 0.19/0.46          | ~ (r2_hidden @ (k3_tarski @ X49) @ X49))),
% 0.19/0.46      inference('clc', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.19/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.19/0.46              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.19/0.46  thf(t4_yellow_1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X50 : $i]: ((k3_yellow_1 @ X50) = (k2_yellow_1 @ (k9_setfam_1 @ X50)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.19/0.46  thf('9', plain, (![X34 : $i]: ((k3_tarski @ (k9_setfam_1 @ X34)) = (X34))),
% 0.19/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.19/0.46          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.46  thf(t4_subset_1, axiom,
% 0.19/0.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.19/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.46  thf('12', plain, (![X48 : $i]: ((k9_setfam_1 @ X48) = (k1_zfmisc_1 @ X48))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X40))),
% 0.19/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf(dt_k3_subset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.46       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X37 : $i, X38 : $i]:
% 0.19/0.46         ((m1_subset_1 @ (k3_subset_1 @ X37 @ X38) @ (k1_zfmisc_1 @ X37))
% 0.19/0.46          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.46  thf('15', plain, (![X48 : $i]: ((k9_setfam_1 @ X48) = (k1_zfmisc_1 @ X48))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('16', plain, (![X48 : $i]: ((k9_setfam_1 @ X48) = (k1_zfmisc_1 @ X48))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X37 : $i, X38 : $i]:
% 0.19/0.46         ((m1_subset_1 @ (k3_subset_1 @ X37 @ X38) @ (k9_setfam_1 @ X37))
% 0.19/0.46          | ~ (m1_subset_1 @ X38 @ (k9_setfam_1 @ X37)))),
% 0.19/0.46      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k9_setfam_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['13', '17'])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X40))),
% 0.19/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf(d5_subset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.46       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X35 : $i, X36 : $i]:
% 0.19/0.46         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 0.19/0.46          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.46  thf('21', plain, (![X48 : $i]: ((k9_setfam_1 @ X48) = (k1_zfmisc_1 @ X48))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X35 : $i, X36 : $i]:
% 0.19/0.46         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 0.19/0.46          | ~ (m1_subset_1 @ X36 @ (k9_setfam_1 @ X35)))),
% 0.19/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['19', '22'])).
% 0.19/0.46  thf(t2_boole, axiom,
% 0.19/0.46    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.46  thf(t12_setfam_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (![X41 : $i, X42 : $i]:
% 0.19/0.46         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.19/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (![X5 : $i]:
% 0.19/0.46         ((k1_setfam_1 @ (k2_tarski @ X5 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.46  thf(t100_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ X3 @ X4)
% 0.19/0.46           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (![X41 : $i, X42 : $i]:
% 0.19/0.46         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.19/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ X3 @ X4)
% 0.19/0.46           = (k5_xboole_0 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.19/0.46      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.46  thf('30', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['26', '29'])).
% 0.19/0.46  thf(t5_boole, axiom,
% 0.19/0.46    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.46  thf('31', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.46  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.46  thf('33', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['23', '32'])).
% 0.19/0.46  thf('34', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k9_setfam_1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['18', '33'])).
% 0.19/0.46  thf(t2_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      (![X43 : $i, X44 : $i]:
% 0.19/0.46         ((r2_hidden @ X43 @ X44)
% 0.19/0.46          | (v1_xboole_0 @ X44)
% 0.19/0.46          | ~ (m1_subset_1 @ X43 @ X44))),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.46  thf('36', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.19/0.46          | (r2_hidden @ X0 @ (k9_setfam_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.46  thf(fc1_subset_1, axiom,
% 0.19/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.46  thf('37', plain, (![X39 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.46  thf('38', plain, (![X48 : $i]: ((k9_setfam_1 @ X48) = (k1_zfmisc_1 @ X48))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('39', plain, (![X39 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X39))),
% 0.19/0.46      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.46  thf('40', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.19/0.46      inference('clc', [status(thm)], ['36', '39'])).
% 0.19/0.46  thf('41', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['10', '40'])).
% 0.19/0.46  thf('42', plain, (((sk_A) != (sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '41'])).
% 0.19/0.46  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
