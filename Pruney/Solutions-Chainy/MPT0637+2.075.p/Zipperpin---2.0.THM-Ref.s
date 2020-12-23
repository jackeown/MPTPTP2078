%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.khp10iyLrM

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 (  83 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  493 ( 603 expanded)
%              Number of equality atoms :   44 (  53 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k7_relat_1 @ X30 @ X31 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X24: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X17 ) @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X24: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('21',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X24: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('30',plain,(
    ! [X25: $i] :
      ( ( ( k5_relat_1 @ X25 @ ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('43',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.khp10iyLrM
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 74 iterations in 0.063s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.19/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.54  thf(t94_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (![X28 : $i, X29 : $i]:
% 0.19/0.54         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 0.19/0.54          | ~ (v1_relat_1 @ X29))),
% 0.19/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.54  thf(t43_funct_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.54       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i]:
% 0.19/0.54        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.54          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.19/0.54         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.19/0.54          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.19/0.54        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.54  thf(fc3_funct_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.54  thf('3', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.19/0.54         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.54  thf(t17_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.54  thf(t71_relat_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.54  thf('6', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.19/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.54  thf(t97_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.54         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      (![X30 : $i, X31 : $i]:
% 0.19/0.54         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.19/0.54          | ((k7_relat_1 @ X30 @ X31) = (X30))
% 0.19/0.54          | ~ (v1_relat_1 @ X30))),
% 0.19/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.54  thf('9', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.54  thf('11', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 0.19/0.54           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      (![X28 : $i, X29 : $i]:
% 0.19/0.54         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 0.19/0.54          | ~ (v1_relat_1 @ X29))),
% 0.19/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      (![X28 : $i, X29 : $i]:
% 0.19/0.54         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 0.19/0.54          | ~ (v1_relat_1 @ X29))),
% 0.19/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.54  thf(t72_relat_1, axiom,
% 0.19/0.54    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (![X24 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X24)) = (k6_relat_1 @ X24))),
% 0.19/0.54      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.54  thf(t54_relat_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( v1_relat_1 @ B ) =>
% 0.19/0.54           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.54             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (![X17 : $i, X18 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X17)
% 0.19/0.54          | ((k4_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 0.19/0.54              = (k5_relat_1 @ (k4_relat_1 @ X17) @ (k4_relat_1 @ X18)))
% 0.19/0.54          | ~ (v1_relat_1 @ X18))),
% 0.19/0.54      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.54            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.19/0.54          | ~ (v1_relat_1 @ X1)
% 0.19/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.54  thf('17', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.54            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.19/0.54          | ~ (v1_relat_1 @ X1))),
% 0.19/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.54            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.19/0.55               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.19/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.19/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['13', '18'])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (![X24 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X24)) = (k6_relat_1 @ X24))),
% 0.19/0.55      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.55  thf('21', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('22', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.55           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.55            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['12', '23'])).
% 0.19/0.55  thf('25', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.55           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.55           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['11', '26'])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      (![X24 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X24)) = (k6_relat_1 @ X24))),
% 0.19/0.55      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.55           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.55  thf(t80_relat_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ A ) =>
% 0.19/0.55       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (![X25 : $i]:
% 0.19/0.55         (((k5_relat_1 @ X25 @ (k6_relat_1 @ (k2_relat_1 @ X25))) = (X25))
% 0.19/0.55          | ~ (v1_relat_1 @ X25))),
% 0.19/0.55      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      (![X28 : $i, X29 : $i]:
% 0.19/0.55         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 0.19/0.55          | ~ (v1_relat_1 @ X29))),
% 0.19/0.55      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 0.19/0.55            = (k6_relat_1 @ X0))
% 0.19/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.55  thf('33', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.19/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.55  thf('34', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('35', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.19/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.55  thf('36', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.19/0.55  thf(t100_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ C ) =>
% 0.19/0.55       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.55         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.55         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 0.19/0.55            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 0.19/0.55          | ~ (v1_relat_1 @ X11))),
% 0.19/0.55      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.55            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.19/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.19/0.55  thf('40', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.55           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.55           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['29', '41'])).
% 0.19/0.55  thf('43', plain,
% 0.19/0.55      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.19/0.55         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.55      inference('demod', [status(thm)], ['4', '42'])).
% 0.19/0.55  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
