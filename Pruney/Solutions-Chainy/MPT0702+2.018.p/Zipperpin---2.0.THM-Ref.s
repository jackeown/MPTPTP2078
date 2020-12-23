%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZuewNGyaOp

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:44 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 151 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  500 (1680 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( r1_tarski @ ( k10_relat_1 @ X19 @ ( k9_relat_1 @ X19 @ X20 ) ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('2',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k10_relat_1 @ X21 @ X22 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X21 ) @ X22 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C_1 @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k9_relat_1 @ X14 @ X12 ) @ ( k9_relat_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( r1_tarski @ ( k10_relat_1 @ X19 @ ( k9_relat_1 @ X19 @ X20 ) ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( r1_tarski @ X17 @ ( k10_relat_1 @ X18 @ ( k9_relat_1 @ X18 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('34',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','31','37'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r2_hidden @ sk_A @ ( k1_zfmisc_1 @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('42',plain,(
    ! [X8: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZuewNGyaOp
% 0.13/0.37  % Computer   : n022.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:58:56 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 114 iterations in 0.081s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(t157_funct_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.37/0.56           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.56         ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.37/0.56              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.56            ( r1_tarski @ A @ B ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.37/0.56  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t152_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( v2_funct_1 @ B ) =>
% 0.37/0.56         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X19)
% 0.37/0.56          | (r1_tarski @ (k10_relat_1 @ X19 @ (k9_relat_1 @ X19 @ X20)) @ X20)
% 0.37/0.56          | ~ (v1_funct_1 @ X19)
% 0.37/0.56          | ~ (v1_relat_1 @ X19))),
% 0.37/0.56      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.37/0.56  thf('2', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d9_funct_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.56       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X15 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X15)
% 0.37/0.56          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 0.37/0.56          | ~ (v1_funct_1 @ X15)
% 0.37/0.56          | ~ (v1_relat_1 @ X15))),
% 0.37/0.56      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      ((~ (v1_funct_1 @ sk_C_1)
% 0.37/0.56        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 0.37/0.56        | ~ (v2_funct_1 @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('6', plain, ((v2_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.37/0.56  thf(t155_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( v2_funct_1 @ B ) =>
% 0.37/0.56         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X21)
% 0.37/0.56          | ((k10_relat_1 @ X21 @ X22)
% 0.37/0.56              = (k9_relat_1 @ (k2_funct_1 @ X21) @ X22))
% 0.37/0.56          | ~ (v1_funct_1 @ X21)
% 0.37/0.56          | ~ (v1_relat_1 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k10_relat_1 @ sk_C_1 @ X0)
% 0.37/0.56            = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.56          | ~ (v2_funct_1 @ sk_C_1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('12', plain, ((v2_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k10_relat_1 @ sk_C_1 @ X0)
% 0.37/0.56           = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t156_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ C ) =>
% 0.37/0.56       ( ( r1_tarski @ A @ B ) =>
% 0.37/0.56         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X12 @ X13)
% 0.37/0.56          | ~ (v1_relat_1 @ X14)
% 0.37/0.56          | (r1_tarski @ (k9_relat_1 @ X14 @ X12) @ (k9_relat_1 @ X14 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.37/0.56           (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_B)))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (((r1_tarski @ 
% 0.37/0.56         (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.37/0.56         (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)))
% 0.37/0.56        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['13', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k10_relat_1 @ sk_C_1 @ X0)
% 0.37/0.56           = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X19)
% 0.37/0.56          | (r1_tarski @ (k10_relat_1 @ X19 @ (k9_relat_1 @ X19 @ X20)) @ X20)
% 0.37/0.56          | ~ (v1_funct_1 @ X19)
% 0.37/0.56          | ~ (v1_relat_1 @ X19))),
% 0.37/0.56      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.37/0.56  thf('20', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t146_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 0.37/0.56          | (r1_tarski @ X17 @ (k10_relat_1 @ X18 @ (k9_relat_1 @ X18 @ X17)))
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56        | (r1_tarski @ sk_A @ 
% 0.37/0.56           (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      ((r1_tarski @ sk_A @ 
% 0.37/0.56        (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X0 : $i, X2 : $i]:
% 0.37/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      ((~ (r1_tarski @ (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.37/0.56           sk_A)
% 0.37/0.56        | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.56        | ~ (v2_funct_1 @ sk_C_1)
% 0.37/0.56        | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '26'])).
% 0.37/0.56  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('29', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('30', plain, ((v2_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)) = (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.37/0.56  thf('32', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.37/0.56  thf(dt_k2_funct_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X16 : $i]:
% 0.37/0.56         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.37/0.56          | ~ (v1_funct_1 @ X16)
% 0.37/0.56          | ~ (v1_relat_1 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C_1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('37', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      ((r1_tarski @ sk_A @ 
% 0.37/0.56        (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['17', '18', '31', '37'])).
% 0.37/0.56  thf(d1_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.37/0.56          | (r2_hidden @ X3 @ X5)
% 0.37/0.56          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      ((r2_hidden @ sk_A @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['38', '40'])).
% 0.37/0.56  thf(t99_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.37/0.56  thf('42', plain, (![X8 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X8)) = (X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.37/0.56  thf(t56_setfam_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.37/0.56       ( r1_tarski @ C @ B ) ))).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k3_tarski @ X9) @ X10)
% 0.37/0.56          | ~ (r2_hidden @ X11 @ X9)
% 0.37/0.56          | (r1_tarski @ X11 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.56          | (r1_tarski @ X2 @ X1)
% 0.37/0.56          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ sk_A @ X0)
% 0.37/0.56          | ~ (r1_tarski @ 
% 0.37/0.56               (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_B)) @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '44'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.56        | ~ (v2_funct_1 @ sk_C_1)
% 0.37/0.56        | (r1_tarski @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '45'])).
% 0.37/0.56  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('49', plain, ((v2_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('50', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.37/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
