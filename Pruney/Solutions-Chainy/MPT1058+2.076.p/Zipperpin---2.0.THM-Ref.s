%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8GeyLQWPJg

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 154 expanded)
%              Number of leaves         :   25 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  583 (1204 expanded)
%              Number of equality atoms :   47 ( 101 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k10_relat_1 @ X3 @ ( k10_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k7_relat_1 @ X11 @ X12 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k10_relat_1 @ X19 @ ( k9_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('32',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k10_relat_1 @ X3 @ ( k10_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','38'])).

thf('40',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','33'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','45'])).

thf('47',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8GeyLQWPJg
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:58:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 39 iterations in 0.033s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(t94_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (((k7_relat_1 @ X10 @ X9) = (k5_relat_1 @ (k6_relat_1 @ X9) @ X10))
% 0.20/0.49          | ~ (v1_relat_1 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.49  thf(t181_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ C ) =>
% 0.20/0.49           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.49             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X2)
% 0.20/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.20/0.49              = (k10_relat_1 @ X3 @ (k10_relat_1 @ X2 @ X4)))
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.20/0.49  thf(t175_funct_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ![B:$i,C:$i]:
% 0.20/0.49         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.49           ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.49             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49          ( ![B:$i,C:$i]:
% 0.20/0.49            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.49              ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.49                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.20/0.49  thf('2', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t71_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('3', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf(t97_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.49         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.49          | ((k7_relat_1 @ X11 @ X12) = (X11))
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf(fc3_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('6', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.49          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 0.20/0.49         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (((k7_relat_1 @ X10 @ X9) = (k5_relat_1 @ (k6_relat_1 @ X9) @ X10))
% 0.20/0.49          | ~ (v1_relat_1 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.49  thf('10', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf(t98_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X13 : $i]:
% 0.20/0.49         (((k7_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (X13))
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf(t87_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X8)) @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf('18', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.49  thf('20', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf(t164_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.49         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.20/0.49          | ~ (v2_funct_1 @ X19)
% 0.20/0.49          | ((k10_relat_1 @ X19 @ (k9_relat_1 @ X19 @ X18)) = (X18))
% 0.20/0.49          | ~ (v1_funct_1 @ X19)
% 0.20/0.49          | ~ (v1_relat_1 @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ((k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1))
% 0.20/0.49          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('24', plain, (![X15 : $i]: (v1_funct_1 @ (k6_relat_1 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf(fc4_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('25', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ((k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49           (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)) = (X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf(t148_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k9_relat_1 @ X0 @ X1))
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf('32', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X2)
% 0.20/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.20/0.49              = (k10_relat_1 @ X3 @ (k10_relat_1 @ X2 @ X4)))
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.20/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.20/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.20/0.49            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '38'])).
% 0.20/0.49  thf('40', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('41', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.20/0.49           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.20/0.49         (k10_relat_1 @ sk_A @ sk_C))
% 0.20/0.49         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '33'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.49         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.49          = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))
% 0.20/0.49        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '45'])).
% 0.20/0.49  thf('47', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.49         = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.49          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '49'])).
% 0.20/0.49  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.49         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.49         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('54', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
