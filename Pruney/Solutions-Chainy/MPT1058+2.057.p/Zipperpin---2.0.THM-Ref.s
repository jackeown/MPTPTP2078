%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cs8ttE0HNe

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:45 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   75 (  92 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  559 ( 766 expanded)
%              Number of equality atoms :   47 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ X5 @ ( sk_D @ X7 @ X6 @ X5 ) )
      | ( X6
        = ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X1 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_B @ ( sk_D @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ~ ( r1_tarski @ X6 @ ( sk_D @ X7 @ X6 @ X5 ) )
      | ( X6
        = ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('7',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('10',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X22 @ X23 ) @ ( k10_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['19','26','27'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('30',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X26 @ X25 ) )
        = ( k10_relat_1 @ X26 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['11','39'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X32 @ X31 ) @ X33 )
        = ( k3_xboole_0 @ X31 @ ( k10_relat_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('42',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cs8ttE0HNe
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:23:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 134 iterations in 0.104s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.57  thf(t175_funct_2, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ![B:$i,C:$i]:
% 0.38/0.57         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.38/0.57           ( ( k10_relat_1 @ A @ C ) =
% 0.38/0.57             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57          ( ![B:$i,C:$i]:
% 0.38/0.57            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.38/0.57              ( ( k10_relat_1 @ A @ C ) =
% 0.38/0.57                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.38/0.57  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.57  thf(t14_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.38/0.57         ( ![D:$i]:
% 0.38/0.57           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.38/0.57             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.38/0.57       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X5 @ X6)
% 0.38/0.57          | ~ (r1_tarski @ X7 @ X6)
% 0.38/0.57          | (r1_tarski @ X5 @ (sk_D @ X7 @ X6 @ X5))
% 0.38/0.57          | ((X6) = (k2_xboole_0 @ X5 @ X7)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 0.38/0.57          | (r1_tarski @ X0 @ (sk_D @ X1 @ X0 @ X0))
% 0.38/0.57          | ~ (r1_tarski @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (((r1_tarski @ sk_B @ (sk_D @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B @ sk_B))
% 0.38/0.57        | ((sk_B) = (k2_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '4'])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X5 @ X6)
% 0.38/0.57          | ~ (r1_tarski @ X7 @ X6)
% 0.38/0.57          | ~ (r1_tarski @ X6 @ (sk_D @ X7 @ X6 @ X5))
% 0.38/0.57          | ((X6) = (k2_xboole_0 @ X5 @ X7)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.38/0.57        | ((sk_B) = (k2_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.38/0.57        | ~ (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.38/0.57        | ~ (r1_tarski @ sk_B @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf('8', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.38/0.57        | ((sk_B) = (k2_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (((sk_B) = (k2_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.57  thf(t71_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.57  thf('12', plain, (![X28 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.57  thf(t169_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X21 : $i]:
% 0.38/0.57         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 0.38/0.57          | ~ (v1_relat_1 @ X21))),
% 0.38/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.38/0.57            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.38/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('15', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.57  thf(fc3_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.57  thf('16', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.57  thf(t175_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ C ) =>
% 0.38/0.57       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.38/0.57         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.57         (((k10_relat_1 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 0.38/0.57            = (k2_xboole_0 @ (k10_relat_1 @ X22 @ X23) @ 
% 0.38/0.57               (k10_relat_1 @ X22 @ X24)))
% 0.38/0.57          | ~ (v1_relat_1 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.38/0.57            = (k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.57  thf(t167_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 0.38/0.57          | ~ (v1_relat_1 @ X19))),
% 0.38/0.57      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.57  thf('23', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.38/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf(t12_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i]:
% 0.38/0.57         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0) = (X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['19', '26', '27'])).
% 0.38/0.57  thf(t43_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.38/0.57       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X34 : $i, X35 : $i]:
% 0.38/0.57         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.38/0.57           = (k6_relat_1 @ (k3_xboole_0 @ X34 @ X35)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.38/0.57  thf('30', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.57  thf(t182_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( v1_relat_1 @ B ) =>
% 0.38/0.57           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.38/0.57             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X25 : $i, X26 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X25)
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X26 @ X25))
% 0.38/0.57              = (k10_relat_1 @ X26 @ (k1_relat_1 @ X25)))
% 0.38/0.57          | ~ (v1_relat_1 @ X26))),
% 0.38/0.57      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.38/0.57            = (k10_relat_1 @ X1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X1)
% 0.38/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.38/0.57            = (k10_relat_1 @ X1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X1))),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.38/0.57            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['29', '34'])).
% 0.38/0.57  thf('36', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.57  thf('37', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['28', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.38/0.57         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.38/0.57      inference('sup+', [status(thm)], ['11', '39'])).
% 0.38/0.57  thf(t139_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ C ) =>
% 0.38/0.57       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.38/0.57         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.57         (((k10_relat_1 @ (k7_relat_1 @ X32 @ X31) @ X33)
% 0.38/0.57            = (k3_xboole_0 @ X31 @ (k10_relat_1 @ X32 @ X33)))
% 0.38/0.57          | ~ (v1_relat_1 @ X32))),
% 0.38/0.57      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.57         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.57          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.38/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.57         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain, ($false),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['40', '45'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
