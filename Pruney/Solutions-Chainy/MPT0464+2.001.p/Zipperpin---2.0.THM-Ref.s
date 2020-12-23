%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IJv1A7yP9D

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:08 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  432 ( 756 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t50_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( v1_relat_1 @ D )
                 => ( ( ( r1_tarski @ A @ B )
                      & ( r1_tarski @ C @ D ) )
                   => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( r1_tarski @ ( k5_relat_1 @ X33 @ X34 ) @ ( k5_relat_1 @ X31 @ X32 ) )
      | ~ ( r1_tarski @ X34 @ X32 )
      | ~ ( r1_tarski @ X33 @ X31 )
      | ~ ( v1_relat_1 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IJv1A7yP9D
% 0.15/0.34  % Computer   : n013.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:32:24 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 3.86/4.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.86/4.04  % Solved by: fo/fo7.sh
% 3.86/4.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.86/4.04  % done 5466 iterations in 3.584s
% 3.86/4.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.86/4.04  % SZS output start Refutation
% 3.86/4.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.86/4.04  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.86/4.04  thf(sk_B_type, type, sk_B: $i).
% 3.86/4.04  thf(sk_C_type, type, sk_C: $i).
% 3.86/4.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.86/4.04  thf(sk_A_type, type, sk_A: $i).
% 3.86/4.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.86/4.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.86/4.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.86/4.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.86/4.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.86/4.04  thf(commutativity_k2_tarski, axiom,
% 3.86/4.04    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.86/4.04  thf('0', plain,
% 3.86/4.04      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 3.86/4.04      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.86/4.04  thf(t12_setfam_1, axiom,
% 3.86/4.04    (![A:$i,B:$i]:
% 3.86/4.04     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.86/4.04  thf('1', plain,
% 3.86/4.04      (![X24 : $i, X25 : $i]:
% 3.86/4.04         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 3.86/4.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.86/4.04  thf('2', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i]:
% 3.86/4.04         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.86/4.04      inference('sup+', [status(thm)], ['0', '1'])).
% 3.86/4.04  thf('3', plain,
% 3.86/4.04      (![X24 : $i, X25 : $i]:
% 3.86/4.04         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 3.86/4.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.86/4.04  thf('4', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.86/4.04      inference('sup+', [status(thm)], ['2', '3'])).
% 3.86/4.04  thf(d10_xboole_0, axiom,
% 3.86/4.04    (![A:$i,B:$i]:
% 3.86/4.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.86/4.04  thf('5', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.86/4.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.86/4.04  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.86/4.04      inference('simplify', [status(thm)], ['5'])).
% 3.86/4.04  thf(t17_xboole_1, axiom,
% 3.86/4.04    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.86/4.04  thf('7', plain,
% 3.86/4.04      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 3.86/4.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.86/4.04  thf(t3_subset, axiom,
% 3.86/4.04    (![A:$i,B:$i]:
% 3.86/4.04     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.86/4.04  thf('8', plain,
% 3.86/4.04      (![X26 : $i, X28 : $i]:
% 3.86/4.04         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 3.86/4.04      inference('cnf', [status(esa)], [t3_subset])).
% 3.86/4.04  thf('9', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i]:
% 3.86/4.04         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.86/4.04      inference('sup-', [status(thm)], ['7', '8'])).
% 3.86/4.04  thf(cc2_relat_1, axiom,
% 3.86/4.04    (![A:$i]:
% 3.86/4.04     ( ( v1_relat_1 @ A ) =>
% 3.86/4.04       ( ![B:$i]:
% 3.86/4.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.86/4.04  thf('10', plain,
% 3.86/4.04      (![X29 : $i, X30 : $i]:
% 3.86/4.04         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 3.86/4.04          | (v1_relat_1 @ X29)
% 3.86/4.04          | ~ (v1_relat_1 @ X30))),
% 3.86/4.04      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.86/4.04  thf('11', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.86/4.04      inference('sup-', [status(thm)], ['9', '10'])).
% 3.86/4.04  thf('12', plain,
% 3.86/4.04      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 3.86/4.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.86/4.04  thf(t50_relat_1, axiom,
% 3.86/4.04    (![A:$i]:
% 3.86/4.04     ( ( v1_relat_1 @ A ) =>
% 3.86/4.04       ( ![B:$i]:
% 3.86/4.04         ( ( v1_relat_1 @ B ) =>
% 3.86/4.04           ( ![C:$i]:
% 3.86/4.04             ( ( v1_relat_1 @ C ) =>
% 3.86/4.04               ( ![D:$i]:
% 3.86/4.04                 ( ( v1_relat_1 @ D ) =>
% 3.86/4.04                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 3.86/4.04                     ( r1_tarski @
% 3.86/4.04                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 3.86/4.04  thf('13', plain,
% 3.86/4.04      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X31)
% 3.86/4.04          | ~ (v1_relat_1 @ X32)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X33 @ X34) @ (k5_relat_1 @ X31 @ X32))
% 3.86/4.04          | ~ (r1_tarski @ X34 @ X32)
% 3.86/4.04          | ~ (r1_tarski @ X33 @ X31)
% 3.86/4.04          | ~ (v1_relat_1 @ X34)
% 3.86/4.04          | ~ (v1_relat_1 @ X33))),
% 3.86/4.04      inference('cnf', [status(esa)], [t50_relat_1])).
% 3.86/4.04  thf('14', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X2)
% 3.86/4.04          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 3.86/4.04          | ~ (r1_tarski @ X2 @ X3)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 3.86/4.04             (k5_relat_1 @ X3 @ X0))
% 3.86/4.04          | ~ (v1_relat_1 @ X0)
% 3.86/4.04          | ~ (v1_relat_1 @ X3))),
% 3.86/4.04      inference('sup-', [status(thm)], ['12', '13'])).
% 3.86/4.04  thf('15', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X1)
% 3.86/4.04          | ~ (v1_relat_1 @ X2)
% 3.86/4.04          | ~ (v1_relat_1 @ X1)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X3 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.86/4.04             (k5_relat_1 @ X2 @ X1))
% 3.86/4.04          | ~ (r1_tarski @ X3 @ X2)
% 3.86/4.04          | ~ (v1_relat_1 @ X3))),
% 3.86/4.04      inference('sup-', [status(thm)], ['11', '14'])).
% 3.86/4.04  thf('16', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X3)
% 3.86/4.04          | ~ (r1_tarski @ X3 @ X2)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X3 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.86/4.04             (k5_relat_1 @ X2 @ X1))
% 3.86/4.04          | ~ (v1_relat_1 @ X2)
% 3.86/4.04          | ~ (v1_relat_1 @ X1))),
% 3.86/4.04      inference('simplify', [status(thm)], ['15'])).
% 3.86/4.04  thf('17', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X1)
% 3.86/4.04          | ~ (v1_relat_1 @ X0)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 3.86/4.04             (k5_relat_1 @ X0 @ X1))
% 3.86/4.04          | ~ (v1_relat_1 @ X0))),
% 3.86/4.04      inference('sup-', [status(thm)], ['6', '16'])).
% 3.86/4.04  thf('18', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.04         ((r1_tarski @ (k5_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 3.86/4.04           (k5_relat_1 @ X0 @ X1))
% 3.86/4.04          | ~ (v1_relat_1 @ X0)
% 3.86/4.04          | ~ (v1_relat_1 @ X1))),
% 3.86/4.04      inference('simplify', [status(thm)], ['17'])).
% 3.86/4.04  thf('19', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.04         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.86/4.04           (k5_relat_1 @ X2 @ X0))
% 3.86/4.04          | ~ (v1_relat_1 @ X0)
% 3.86/4.04          | ~ (v1_relat_1 @ X2))),
% 3.86/4.04      inference('sup+', [status(thm)], ['4', '18'])).
% 3.86/4.04  thf('20', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.04         ((r1_tarski @ (k5_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 3.86/4.04           (k5_relat_1 @ X0 @ X1))
% 3.86/4.04          | ~ (v1_relat_1 @ X0)
% 3.86/4.04          | ~ (v1_relat_1 @ X1))),
% 3.86/4.04      inference('simplify', [status(thm)], ['17'])).
% 3.86/4.04  thf(t19_xboole_1, axiom,
% 3.86/4.04    (![A:$i,B:$i,C:$i]:
% 3.86/4.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 3.86/4.04       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.86/4.04  thf('21', plain,
% 3.86/4.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.86/4.04         (~ (r1_tarski @ X5 @ X6)
% 3.86/4.04          | ~ (r1_tarski @ X5 @ X7)
% 3.86/4.04          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 3.86/4.04      inference('cnf', [status(esa)], [t19_xboole_1])).
% 3.86/4.04  thf('22', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X0)
% 3.86/4.04          | ~ (v1_relat_1 @ X1)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 3.86/4.04             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 3.86/4.04          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 3.86/4.04      inference('sup-', [status(thm)], ['20', '21'])).
% 3.86/4.04  thf('23', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X1)
% 3.86/4.04          | ~ (v1_relat_1 @ X0)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 3.86/4.04             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 3.86/4.04          | ~ (v1_relat_1 @ X1)
% 3.86/4.04          | ~ (v1_relat_1 @ X2))),
% 3.86/4.04      inference('sup-', [status(thm)], ['19', '22'])).
% 3.86/4.04  thf('24', plain,
% 3.86/4.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.04         (~ (v1_relat_1 @ X2)
% 3.86/4.04          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 3.86/4.04             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 3.86/4.04          | ~ (v1_relat_1 @ X0)
% 3.86/4.04          | ~ (v1_relat_1 @ X1))),
% 3.86/4.04      inference('simplify', [status(thm)], ['23'])).
% 3.86/4.04  thf(t52_relat_1, conjecture,
% 3.86/4.04    (![A:$i]:
% 3.86/4.04     ( ( v1_relat_1 @ A ) =>
% 3.86/4.04       ( ![B:$i]:
% 3.86/4.04         ( ( v1_relat_1 @ B ) =>
% 3.86/4.04           ( ![C:$i]:
% 3.86/4.04             ( ( v1_relat_1 @ C ) =>
% 3.86/4.04               ( r1_tarski @
% 3.86/4.04                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 3.86/4.04                 ( k3_xboole_0 @
% 3.86/4.04                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.86/4.04  thf(zf_stmt_0, negated_conjecture,
% 3.86/4.04    (~( ![A:$i]:
% 3.86/4.04        ( ( v1_relat_1 @ A ) =>
% 3.86/4.04          ( ![B:$i]:
% 3.86/4.04            ( ( v1_relat_1 @ B ) =>
% 3.86/4.04              ( ![C:$i]:
% 3.86/4.04                ( ( v1_relat_1 @ C ) =>
% 3.86/4.04                  ( r1_tarski @
% 3.86/4.04                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 3.86/4.04                    ( k3_xboole_0 @
% 3.86/4.04                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 3.86/4.04    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 3.86/4.04  thf('25', plain,
% 3.86/4.04      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 3.86/4.04          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 3.86/4.04           (k5_relat_1 @ sk_A @ sk_C)))),
% 3.86/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.04  thf('26', plain,
% 3.86/4.04      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 3.86/4.04      inference('sup-', [status(thm)], ['24', '25'])).
% 3.86/4.04  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 3.86/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.04  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 3.86/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.04  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 3.86/4.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.04  thf('30', plain, ($false),
% 3.86/4.04      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.86/4.04  
% 3.86/4.04  % SZS output end Refutation
% 3.86/4.04  
% 3.86/4.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
