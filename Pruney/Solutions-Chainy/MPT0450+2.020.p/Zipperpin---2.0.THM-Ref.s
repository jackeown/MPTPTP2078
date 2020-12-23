%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UdJVQSL4XU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:04 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 126 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  485 ( 945 expanded)
%              Number of equality atoms :   17 (  62 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X10 ) ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( r1_tarski @ ( k3_relat_1 @ X39 ) @ ( k3_relat_1 @ X38 ) )
      | ~ ( r1_tarski @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_relat_1 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( r1_tarski @ ( k3_relat_1 @ X39 ) @ ( k3_relat_1 @ X38 ) )
      | ~ ( r1_tarski @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_relat_1 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','31'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('34',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UdJVQSL4XU
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:42:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.48/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.73  % Solved by: fo/fo7.sh
% 0.48/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.73  % done 479 iterations in 0.265s
% 0.48/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.73  % SZS output start Refutation
% 0.48/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.73  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.48/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.73  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.73  thf('0', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.73  thf(t12_setfam_1, axiom,
% 0.48/0.73    (![A:$i,B:$i]:
% 0.48/0.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.73  thf('1', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('2', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.48/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.73  thf(t22_xboole_1, axiom,
% 0.48/0.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.48/0.73  thf('3', plain,
% 0.48/0.73      (![X6 : $i, X7 : $i]:
% 0.48/0.73         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.48/0.73      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.48/0.73  thf('4', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('5', plain,
% 0.48/0.73      (![X6 : $i, X7 : $i]:
% 0.48/0.73         ((k2_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))) = (X6))),
% 0.48/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.48/0.73  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.73      inference('sup+', [status(thm)], ['2', '5'])).
% 0.48/0.73  thf(t31_xboole_1, axiom,
% 0.48/0.73    (![A:$i,B:$i,C:$i]:
% 0.48/0.73     ( r1_tarski @
% 0.48/0.73       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.48/0.73       ( k2_xboole_0 @ B @ C ) ))).
% 0.48/0.73  thf('7', plain,
% 0.48/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.73         (r1_tarski @ 
% 0.48/0.73          (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)) @ 
% 0.48/0.73          (k2_xboole_0 @ X9 @ X10))),
% 0.48/0.73      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.48/0.73  thf('8', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('9', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('10', plain,
% 0.48/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.73         (r1_tarski @ 
% 0.48/0.73          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ 
% 0.48/0.73           (k1_setfam_1 @ (k2_tarski @ X8 @ X10))) @ 
% 0.48/0.73          (k2_xboole_0 @ X9 @ X10))),
% 0.48/0.73      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.48/0.73  thf('11', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.48/0.73          (k2_xboole_0 @ X0 @ X0))),
% 0.48/0.73      inference('sup+', [status(thm)], ['6', '10'])).
% 0.48/0.73  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.73      inference('sup+', [status(thm)], ['2', '5'])).
% 0.48/0.73  thf('13', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.48/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.48/0.73  thf(t31_relat_1, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( v1_relat_1 @ A ) =>
% 0.48/0.73       ( ![B:$i]:
% 0.48/0.73         ( ( v1_relat_1 @ B ) =>
% 0.48/0.73           ( ( r1_tarski @ A @ B ) =>
% 0.48/0.73             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.48/0.73  thf('14', plain,
% 0.48/0.73      (![X38 : $i, X39 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X38)
% 0.48/0.73          | (r1_tarski @ (k3_relat_1 @ X39) @ (k3_relat_1 @ X38))
% 0.48/0.73          | ~ (r1_tarski @ X39 @ X38)
% 0.48/0.73          | ~ (v1_relat_1 @ X39))),
% 0.48/0.73      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.48/0.73  thf('15', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.48/0.73          | (r1_tarski @ 
% 0.48/0.73             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.73             (k3_relat_1 @ X0))
% 0.48/0.73          | ~ (v1_relat_1 @ X0))),
% 0.48/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.73  thf('16', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.48/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.48/0.73  thf(t3_subset, axiom,
% 0.48/0.73    (![A:$i,B:$i]:
% 0.48/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.73  thf('17', plain,
% 0.48/0.73      (![X33 : $i, X35 : $i]:
% 0.48/0.73         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 0.48/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.73  thf('18', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.48/0.73          (k1_zfmisc_1 @ X0))),
% 0.48/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.73  thf(cc2_relat_1, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( v1_relat_1 @ A ) =>
% 0.48/0.73       ( ![B:$i]:
% 0.48/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.73  thf('19', plain,
% 0.48/0.73      (![X36 : $i, X37 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.48/0.73          | (v1_relat_1 @ X36)
% 0.48/0.73          | ~ (v1_relat_1 @ X37))),
% 0.48/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.73  thf('20', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X0)
% 0.48/0.73          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.48/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.73  thf('21', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X0)
% 0.48/0.73          | (r1_tarski @ 
% 0.48/0.73             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.73             (k3_relat_1 @ X0)))),
% 0.48/0.73      inference('clc', [status(thm)], ['15', '20'])).
% 0.48/0.73  thf(t17_xboole_1, axiom,
% 0.48/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.73  thf('22', plain,
% 0.48/0.73      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.48/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.48/0.73  thf('23', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('24', plain,
% 0.48/0.73      (![X1 : $i, X2 : $i]:
% 0.48/0.73         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2)) @ X1)),
% 0.48/0.73      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.73  thf('25', plain,
% 0.48/0.73      (![X38 : $i, X39 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X38)
% 0.48/0.73          | (r1_tarski @ (k3_relat_1 @ X39) @ (k3_relat_1 @ X38))
% 0.48/0.73          | ~ (r1_tarski @ X39 @ X38)
% 0.48/0.73          | ~ (v1_relat_1 @ X39))),
% 0.48/0.73      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.48/0.73  thf('26', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.48/0.73          | (r1_tarski @ 
% 0.48/0.73             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.73             (k3_relat_1 @ X0))
% 0.48/0.73          | ~ (v1_relat_1 @ X0))),
% 0.48/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.73  thf('27', plain,
% 0.48/0.73      (![X1 : $i, X2 : $i]:
% 0.48/0.73         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2)) @ X1)),
% 0.48/0.73      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.73  thf('28', plain,
% 0.48/0.73      (![X33 : $i, X35 : $i]:
% 0.48/0.73         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 0.48/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.73  thf('29', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.48/0.73          (k1_zfmisc_1 @ X0))),
% 0.48/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.73  thf('30', plain,
% 0.48/0.73      (![X36 : $i, X37 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.48/0.73          | (v1_relat_1 @ X36)
% 0.48/0.73          | ~ (v1_relat_1 @ X37))),
% 0.48/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.73  thf('31', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X0)
% 0.48/0.73          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.48/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.73  thf('32', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X0)
% 0.48/0.73          | (r1_tarski @ 
% 0.48/0.73             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.73             (k3_relat_1 @ X0)))),
% 0.48/0.73      inference('clc', [status(thm)], ['26', '31'])).
% 0.48/0.73  thf(t19_xboole_1, axiom,
% 0.48/0.73    (![A:$i,B:$i,C:$i]:
% 0.48/0.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.48/0.73       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.48/0.73  thf('33', plain,
% 0.48/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.73         (~ (r1_tarski @ X3 @ X4)
% 0.48/0.73          | ~ (r1_tarski @ X3 @ X5)
% 0.48/0.73          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.48/0.73      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.48/0.73  thf('34', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('35', plain,
% 0.48/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.73         (~ (r1_tarski @ X3 @ X4)
% 0.48/0.73          | ~ (r1_tarski @ X3 @ X5)
% 0.48/0.73          | (r1_tarski @ X3 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.48/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.48/0.73  thf('36', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X0)
% 0.48/0.73          | (r1_tarski @ 
% 0.48/0.73             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.73             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X0) @ X2)))
% 0.48/0.73          | ~ (r1_tarski @ 
% 0.48/0.73               (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.48/0.73      inference('sup-', [status(thm)], ['32', '35'])).
% 0.48/0.73  thf('37', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i]:
% 0.48/0.73         (~ (v1_relat_1 @ X0)
% 0.48/0.73          | (r1_tarski @ 
% 0.48/0.73             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.73             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 0.48/0.73          | ~ (v1_relat_1 @ X1))),
% 0.48/0.73      inference('sup-', [status(thm)], ['21', '36'])).
% 0.48/0.73  thf(t34_relat_1, conjecture,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( v1_relat_1 @ A ) =>
% 0.48/0.73       ( ![B:$i]:
% 0.48/0.73         ( ( v1_relat_1 @ B ) =>
% 0.48/0.73           ( r1_tarski @
% 0.48/0.73             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.48/0.73             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.48/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.73    (~( ![A:$i]:
% 0.48/0.73        ( ( v1_relat_1 @ A ) =>
% 0.48/0.73          ( ![B:$i]:
% 0.48/0.73            ( ( v1_relat_1 @ B ) =>
% 0.48/0.73              ( r1_tarski @
% 0.48/0.73                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.48/0.73                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.48/0.73    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.48/0.73  thf('38', plain,
% 0.48/0.73      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.48/0.73          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('39', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('40', plain,
% 0.48/0.73      (![X31 : $i, X32 : $i]:
% 0.48/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.48/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.73  thf('41', plain,
% 0.48/0.73      (~ (r1_tarski @ 
% 0.48/0.73          (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.48/0.73          (k1_setfam_1 @ 
% 0.48/0.73           (k2_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 0.48/0.73      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.48/0.73  thf('42', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.48/0.73      inference('sup-', [status(thm)], ['37', '41'])).
% 0.48/0.73  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('45', plain, ($false),
% 0.48/0.73      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.48/0.73  
% 0.48/0.73  % SZS output end Refutation
% 0.48/0.73  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
