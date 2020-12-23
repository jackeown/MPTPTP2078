%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KoOu35B85W

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:09 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 178 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  813 (1713 expanded)
%              Number of equality atoms :   43 ( 105 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k9_relat_1 @ X3 @ ( k9_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( r1_tarski @ ( k10_relat_1 @ X15 @ ( k9_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','6'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['0','6'])).

thf('32',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X6 @ X7 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k9_relat_1 @ X3 @ ( k9_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['31','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k10_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t160_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['30','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KoOu35B85W
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 228 iterations in 0.300s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.80  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.80  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.80  thf(t164_funct_1, conjecture,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.80       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.59/0.80         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i]:
% 0.59/0.80        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.80          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.59/0.80            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.59/0.80  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t71_relat_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.59/0.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.59/0.80  thf('1', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.80  thf(t147_funct_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.80       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.59/0.80         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 0.59/0.80          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 0.59/0.80          | ~ (v1_funct_1 @ X14)
% 0.59/0.80          | ~ (v1_relat_1 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_tarski @ X1 @ X0)
% 0.59/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.59/0.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.59/0.80          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.80  thf(fc3_funct_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.59/0.80       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.59/0.80  thf('4', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('5', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_tarski @ X1 @ X0)
% 0.59/0.80          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (((k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.59/0.80         (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)) = (
% 0.59/0.80         sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '6'])).
% 0.59/0.80  thf(t78_relat_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( v1_relat_1 @ A ) =>
% 0.59/0.80       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X10 : $i]:
% 0.59/0.80         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.59/0.80          | ~ (v1_relat_1 @ X10))),
% 0.59/0.80      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.59/0.80  thf(t159_relat_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( v1_relat_1 @ B ) =>
% 0.59/0.80       ( ![C:$i]:
% 0.59/0.80         ( ( v1_relat_1 @ C ) =>
% 0.59/0.80           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.59/0.80             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (v1_relat_1 @ X3)
% 0.59/0.80          | ((k9_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.59/0.80              = (k9_relat_1 @ X3 @ (k9_relat_1 @ X4 @ X5)))
% 0.59/0.80          | ~ (v1_relat_1 @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (((k9_relat_1 @ X0 @ X1)
% 0.59/0.80            = (k9_relat_1 @ X0 @ 
% 0.59/0.80               (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))
% 0.59/0.80          | ~ (v1_relat_1 @ X0)
% 0.59/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.59/0.80          | ~ (v1_relat_1 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.80  thf('11', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (((k9_relat_1 @ X0 @ X1)
% 0.59/0.80            = (k9_relat_1 @ X0 @ 
% 0.59/0.80               (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))
% 0.59/0.80          | ~ (v1_relat_1 @ X0)
% 0.59/0.80          | ~ (v1_relat_1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_relat_1 @ X0)
% 0.59/0.80          | ((k9_relat_1 @ X0 @ X1)
% 0.59/0.80              = (k9_relat_1 @ X0 @ 
% 0.59/0.80                 (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['12'])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      ((((k9_relat_1 @ sk_B @ 
% 0.59/0.80          (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))
% 0.59/0.80          = (k9_relat_1 @ sk_B @ sk_A))
% 0.59/0.80        | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.80      inference('sup+', [status(thm)], ['7', '13'])).
% 0.59/0.80  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (((k9_relat_1 @ sk_B @ 
% 0.59/0.80         (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))
% 0.59/0.80         = (k9_relat_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_relat_1 @ X0)
% 0.59/0.80          | ((k9_relat_1 @ X0 @ X1)
% 0.59/0.80              = (k9_relat_1 @ X0 @ 
% 0.59/0.80                 (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['12'])).
% 0.59/0.80  thf(t152_funct_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.80       ( ( v2_funct_1 @ B ) =>
% 0.59/0.80         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         (~ (v2_funct_1 @ X15)
% 0.59/0.80          | (r1_tarski @ (k10_relat_1 @ X15 @ (k9_relat_1 @ X15 @ X16)) @ X16)
% 0.59/0.80          | ~ (v1_funct_1 @ X15)
% 0.59/0.80          | ~ (v1_relat_1 @ X15))),
% 0.59/0.80      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.59/0.80           (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X0))
% 0.59/0.80          | ~ (v1_relat_1 @ X1)
% 0.59/0.80          | ~ (v1_relat_1 @ X1)
% 0.59/0.80          | ~ (v1_funct_1 @ X1)
% 0.59/0.80          | ~ (v2_funct_1 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v2_funct_1 @ X1)
% 0.59/0.80          | ~ (v1_funct_1 @ X1)
% 0.59/0.80          | ~ (v1_relat_1 @ X1)
% 0.59/0.80          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.59/0.80             (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X0)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['19'])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.59/0.80         (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.59/0.80          (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)))
% 0.59/0.80        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.80        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.80        | ~ (v2_funct_1 @ sk_B))),
% 0.59/0.80      inference('sup+', [status(thm)], ['16', '20'])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (((k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.59/0.80         (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)) = (
% 0.59/0.80         sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '6'])).
% 0.59/0.80  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('25', plain, ((v2_funct_1 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.59/0.80      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.59/0.80  thf(d10_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X0 : $i, X2 : $i]:
% 0.59/0.80         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      ((~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.59/0.80        | ((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      (((k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.59/0.80         (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)) = (
% 0.59/0.80         sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '6'])).
% 0.59/0.80  thf('32', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.80  thf(t167_relat_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( v1_relat_1 @ B ) =>
% 0.59/0.80       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i]:
% 0.59/0.80         ((r1_tarski @ (k10_relat_1 @ X6 @ X7) @ (k1_relat_1 @ X6))
% 0.59/0.80          | ~ (v1_relat_1 @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.59/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.80  thf('35', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.59/0.80      inference('demod', [status(thm)], ['34', '35'])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_tarski @ X1 @ X0)
% 0.59/0.80          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80           (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.59/0.80           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.80  thf('39', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X10 : $i]:
% 0.59/0.80         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.59/0.80          | ~ (v1_relat_1 @ X10))),
% 0.59/0.80      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.59/0.80            = (k6_relat_1 @ X0))
% 0.59/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.80  thf('42', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.59/0.80           = (k6_relat_1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (v1_relat_1 @ X3)
% 0.59/0.80          | ((k9_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.59/0.80              = (k9_relat_1 @ X3 @ (k9_relat_1 @ X4 @ X5)))
% 0.59/0.80          | ~ (v1_relat_1 @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.59/0.80            = (k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80               (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.59/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.59/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['43', '44'])).
% 0.59/0.80  thf('46', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('47', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.59/0.80           = (k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.59/0.80           (k10_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.59/0.80            (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.59/0.80           = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.59/0.80              (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['38', '48'])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80           (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.59/0.80            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.59/0.80           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.59/0.80           (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.59/0.80           = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['49', '50'])).
% 0.59/0.80  thf('52', plain,
% 0.59/0.80      (((k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['31', '51'])).
% 0.59/0.80  thf('53', plain,
% 0.59/0.80      (![X10 : $i]:
% 0.59/0.80         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 0.59/0.80          | ~ (v1_relat_1 @ X10))),
% 0.59/0.80      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.59/0.80  thf('54', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.80  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.80      inference('simplify', [status(thm)], ['54'])).
% 0.59/0.80  thf('56', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.80  thf(t160_funct_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( v1_relat_1 @ B ) =>
% 0.59/0.80       ( ![C:$i]:
% 0.59/0.80         ( ( v1_relat_1 @ C ) =>
% 0.59/0.80           ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) ) =>
% 0.59/0.80             ( r1_tarski @
% 0.59/0.80               ( k10_relat_1 @ B @ A ) @ 
% 0.59/0.80               ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) ))).
% 0.59/0.80  thf('57', plain,
% 0.59/0.80      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.80         (~ (v1_relat_1 @ X17)
% 0.59/0.80          | (r1_tarski @ (k10_relat_1 @ X18 @ X19) @ 
% 0.59/0.80             (k10_relat_1 @ (k5_relat_1 @ X18 @ X17) @ (k9_relat_1 @ X17 @ X19)))
% 0.59/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X18) @ (k1_relat_1 @ X17))
% 0.59/0.80          | ~ (v1_relat_1 @ X18))),
% 0.59/0.80      inference('cnf', [status(esa)], [t160_funct_1])).
% 0.59/0.80  thf('58', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.59/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.59/0.80          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.59/0.80             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.59/0.80              (k9_relat_1 @ X1 @ X2)))
% 0.59/0.80          | ~ (v1_relat_1 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['56', '57'])).
% 0.59/0.80  thf('59', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.59/0.80          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.59/0.80             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.59/0.80              (k9_relat_1 @ X1 @ X2)))
% 0.59/0.80          | ~ (v1_relat_1 @ X1))),
% 0.59/0.80      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.80  thf('61', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_relat_1 @ X0)
% 0.59/0.80          | (r1_tarski @ 
% 0.59/0.80             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1) @ 
% 0.59/0.80             (k10_relat_1 @ 
% 0.59/0.80              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 0.59/0.80              (k9_relat_1 @ X0 @ X1))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['55', '60'])).
% 0.59/0.80  thf('62', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1) @ 
% 0.59/0.80           (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)))
% 0.59/0.80          | ~ (v1_relat_1 @ X0)
% 0.59/0.80          | ~ (v1_relat_1 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['53', '61'])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_relat_1 @ X0)
% 0.59/0.80          | (r1_tarski @ 
% 0.59/0.80             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1) @ 
% 0.59/0.80             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['62'])).
% 0.59/0.80  thf('64', plain,
% 0.59/0.80      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.59/0.80        | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.80      inference('sup+', [status(thm)], ['52', '63'])).
% 0.59/0.80  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['64', '65'])).
% 0.59/0.80  thf('67', plain, ($false), inference('demod', [status(thm)], ['30', '66'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
