%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oxkjthwn4f

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:05 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 493 expanded)
%              Number of leaves         :   41 ( 169 expanded)
%              Depth                    :   37
%              Number of atoms          : 1656 (4734 expanded)
%              Number of equality atoms :   76 ( 246 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X47 @ ( k1_relat_1 @ X48 ) )
      | ( r1_tarski @ X47 @ ( k10_relat_1 @ X48 @ ( k9_relat_1 @ X48 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('11',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ X49 @ ( k2_relat_1 @ X50 ) )
      | ( ( k9_relat_1 @ X50 @ ( k10_relat_1 @ X50 @ X49 ) )
        = X49 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k9_relat_1 @ X28 @ X29 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k10_relat_1 @ X52 @ X51 ) )
        = ( k3_xboole_0 @ X51 @ ( k9_relat_1 @ X52 @ ( k1_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X57 ) @ ( k6_relat_1 @ X56 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) )
        = ( k10_relat_1 @ X36 @ ( k1_relat_1 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('43',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('48',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('50',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('55',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('60',plain,(
    ! [X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X47 @ ( k1_relat_1 @ X48 ) )
      | ( r1_tarski @ X47 @ ( k10_relat_1 @ X48 @ ( k9_relat_1 @ X48 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('68',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','87'])).

thf('89',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','52'])).

thf('95',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','91','92'])).

thf('99',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','101'])).

thf('103',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('104',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k10_relat_1 @ X52 @ X51 ) )
        = ( k3_xboole_0 @ X51 @ ( k9_relat_1 @ X52 @ ( k1_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['111','114','115','116'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('118',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r1_tarski @ X53 @ X54 )
      | ~ ( v1_relat_1 @ X55 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v2_funct_1 @ X55 )
      | ~ ( r1_tarski @ X53 @ ( k1_relat_1 @ X55 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X55 @ X53 ) @ ( k9_relat_1 @ X55 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('133',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) )
        = ( k10_relat_1 @ X36 @ ( k1_relat_1 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('135',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_xboole_0 @ X33 @ X34 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k2_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k2_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','137'])).

thf('139',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('140',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('143',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['138','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','144'])).

thf('146',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','52'])).

thf('154',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r1_tarski @ X53 @ X54 )
      | ~ ( v1_relat_1 @ X55 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v2_funct_1 @ X55 )
      | ~ ( r1_tarski @ X53 @ ( k1_relat_1 @ X55 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X55 @ X53 ) @ ( k9_relat_1 @ X55 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['8','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oxkjthwn4f
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.95/2.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.95/2.12  % Solved by: fo/fo7.sh
% 1.95/2.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.95/2.12  % done 2615 iterations in 1.666s
% 1.95/2.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.95/2.12  % SZS output start Refutation
% 1.95/2.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.95/2.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.95/2.12  thf(sk_B_type, type, sk_B: $i).
% 1.95/2.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.95/2.12  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.95/2.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.95/2.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.95/2.12  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.95/2.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.95/2.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.95/2.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.95/2.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.95/2.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.95/2.12  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.95/2.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.95/2.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.95/2.12  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.95/2.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.95/2.12  thf(sk_A_type, type, sk_A: $i).
% 1.95/2.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.95/2.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.95/2.12  thf(t164_funct_1, conjecture,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.95/2.12       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.95/2.12         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.95/2.12  thf(zf_stmt_0, negated_conjecture,
% 1.95/2.12    (~( ![A:$i,B:$i]:
% 1.95/2.12        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.95/2.12          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.95/2.12            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 1.95/2.12    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 1.95/2.12  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf(t146_funct_1, axiom,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( v1_relat_1 @ B ) =>
% 1.95/2.12       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.95/2.12         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.95/2.12  thf('1', plain,
% 1.95/2.12      (![X47 : $i, X48 : $i]:
% 1.95/2.12         (~ (r1_tarski @ X47 @ (k1_relat_1 @ X48))
% 1.95/2.12          | (r1_tarski @ X47 @ (k10_relat_1 @ X48 @ (k9_relat_1 @ X48 @ X47)))
% 1.95/2.12          | ~ (v1_relat_1 @ X48))),
% 1.95/2.12      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.95/2.12  thf('2', plain,
% 1.95/2.12      ((~ (v1_relat_1 @ sk_B)
% 1.95/2.12        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.95/2.12      inference('sup-', [status(thm)], ['0', '1'])).
% 1.95/2.12  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('4', plain,
% 1.95/2.12      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.95/2.12      inference('demod', [status(thm)], ['2', '3'])).
% 1.95/2.12  thf(d10_xboole_0, axiom,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.95/2.12  thf('5', plain,
% 1.95/2.12      (![X8 : $i, X10 : $i]:
% 1.95/2.12         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.95/2.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.12  thf('6', plain,
% 1.95/2.12      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 1.95/2.12        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['4', '5'])).
% 1.95/2.12  thf('7', plain,
% 1.95/2.12      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('8', plain,
% 1.95/2.12      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 1.95/2.12      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 1.95/2.12  thf(t71_relat_1, axiom,
% 1.95/2.12    (![A:$i]:
% 1.95/2.12     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.95/2.12       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.95/2.12  thf('9', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 1.95/2.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.95/2.12  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.95/2.12  thf('10', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 1.95/2.12      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.95/2.12  thf(t147_funct_1, axiom,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.95/2.12       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.95/2.12         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.95/2.12  thf('11', plain,
% 1.95/2.12      (![X49 : $i, X50 : $i]:
% 1.95/2.12         (~ (r1_tarski @ X49 @ (k2_relat_1 @ X50))
% 1.95/2.12          | ((k9_relat_1 @ X50 @ (k10_relat_1 @ X50 @ X49)) = (X49))
% 1.95/2.12          | ~ (v1_funct_1 @ X50)
% 1.95/2.12          | ~ (v1_relat_1 @ X50))),
% 1.95/2.12      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.95/2.12  thf('12', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (v1_relat_1 @ X0)
% 1.95/2.12          | ~ (v1_funct_1 @ X0)
% 1.95/2.12          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 1.95/2.12              = (k1_xboole_0)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['10', '11'])).
% 1.95/2.12  thf(t151_relat_1, axiom,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( v1_relat_1 @ B ) =>
% 1.95/2.12       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.95/2.12         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.95/2.12  thf('13', plain,
% 1.95/2.12      (![X28 : $i, X29 : $i]:
% 1.95/2.12         (((k9_relat_1 @ X28 @ X29) != (k1_xboole_0))
% 1.95/2.12          | (r1_xboole_0 @ (k1_relat_1 @ X28) @ X29)
% 1.95/2.12          | ~ (v1_relat_1 @ X28))),
% 1.95/2.12      inference('cnf', [status(esa)], [t151_relat_1])).
% 1.95/2.12  thf('14', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (((k1_xboole_0) != (k1_xboole_0))
% 1.95/2.12          | ~ (v1_funct_1 @ X0)
% 1.95/2.12          | ~ (v1_relat_1 @ X0)
% 1.95/2.12          | ~ (v1_relat_1 @ X0)
% 1.95/2.12          | (r1_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['12', '13'])).
% 1.95/2.12  thf('15', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 1.95/2.12          | ~ (v1_relat_1 @ X0)
% 1.95/2.12          | ~ (v1_funct_1 @ X0))),
% 1.95/2.12      inference('simplify', [status(thm)], ['14'])).
% 1.95/2.12  thf(t3_xboole_0, axiom,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.95/2.12            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.95/2.12       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.95/2.12            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.95/2.12  thf('16', plain,
% 1.95/2.13      (![X4 : $i, X5 : $i]:
% 1.95/2.13         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 1.95/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.95/2.13  thf('17', plain,
% 1.95/2.13      (![X4 : $i, X5 : $i]:
% 1.95/2.13         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 1.95/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.95/2.13  thf('18', plain,
% 1.95/2.13      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.95/2.13         (~ (r2_hidden @ X6 @ X4)
% 1.95/2.13          | ~ (r2_hidden @ X6 @ X7)
% 1.95/2.13          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.95/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.95/2.13  thf('19', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         ((r1_xboole_0 @ X1 @ X0)
% 1.95/2.13          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.95/2.13          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.95/2.13      inference('sup-', [status(thm)], ['17', '18'])).
% 1.95/2.13  thf('20', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_xboole_0 @ X0 @ X1)
% 1.95/2.13          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.95/2.13          | (r1_xboole_0 @ X0 @ X1))),
% 1.95/2.13      inference('sup-', [status(thm)], ['16', '19'])).
% 1.95/2.13  thf('21', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.95/2.13      inference('simplify', [status(thm)], ['20'])).
% 1.95/2.13  thf('22', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v1_funct_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ k1_xboole_0) @ (k1_relat_1 @ X0)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['15', '21'])).
% 1.95/2.13  thf(d3_tarski, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( r1_tarski @ A @ B ) <=>
% 1.95/2.13       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.95/2.13  thf('23', plain,
% 1.95/2.13      (![X1 : $i, X3 : $i]:
% 1.95/2.13         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.95/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.95/2.13  thf(t167_relat_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( v1_relat_1 @ B ) =>
% 1.95/2.13       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.95/2.13  thf('24', plain,
% 1.95/2.13      (![X30 : $i, X31 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 1.95/2.13          | ~ (v1_relat_1 @ X30))),
% 1.95/2.13      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.95/2.13  thf('25', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (~ (r2_hidden @ X0 @ X1)
% 1.95/2.13          | (r2_hidden @ X0 @ X2)
% 1.95/2.13          | ~ (r1_tarski @ X1 @ X2))),
% 1.95/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.95/2.13  thf('26', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 1.95/2.13          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X0 @ X1)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['24', '25'])).
% 1.95/2.13  thf('27', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 1.95/2.13          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.95/2.13             (k1_relat_1 @ X1))
% 1.95/2.13          | ~ (v1_relat_1 @ X1))),
% 1.95/2.13      inference('sup-', [status(thm)], ['23', '26'])).
% 1.95/2.13  thf('28', plain,
% 1.95/2.13      (![X1 : $i, X3 : $i]:
% 1.95/2.13         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.95/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.95/2.13  thf('29', plain,
% 1.95/2.13      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.95/2.13         (~ (r2_hidden @ X6 @ X4)
% 1.95/2.13          | ~ (r2_hidden @ X6 @ X7)
% 1.95/2.13          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.95/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.95/2.13  thf('30', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         ((r1_tarski @ X0 @ X1)
% 1.95/2.13          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.95/2.13          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.95/2.13      inference('sup-', [status(thm)], ['28', '29'])).
% 1.95/2.13  thf('31', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 1.95/2.13          | ~ (r1_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.95/2.13          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2))),
% 1.95/2.13      inference('sup-', [status(thm)], ['27', '30'])).
% 1.95/2.13  thf('32', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (~ (r1_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.95/2.13          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('simplify', [status(thm)], ['31'])).
% 1.95/2.13  thf('33', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_funct_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1))),
% 1.95/2.13      inference('sup-', [status(thm)], ['22', '32'])).
% 1.95/2.13  thf('34', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1)
% 1.95/2.13          | ~ (v1_funct_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('simplify', [status(thm)], ['33'])).
% 1.95/2.13  thf(t148_funct_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.95/2.13       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 1.95/2.13         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 1.95/2.13  thf('35', plain,
% 1.95/2.13      (![X51 : $i, X52 : $i]:
% 1.95/2.13         (((k9_relat_1 @ X52 @ (k10_relat_1 @ X52 @ X51))
% 1.95/2.13            = (k3_xboole_0 @ X51 @ (k9_relat_1 @ X52 @ (k1_relat_1 @ X52))))
% 1.95/2.13          | ~ (v1_funct_1 @ X52)
% 1.95/2.13          | ~ (v1_relat_1 @ X52))),
% 1.95/2.13      inference('cnf', [status(esa)], [t148_funct_1])).
% 1.95/2.13  thf(commutativity_k2_tarski, axiom,
% 1.95/2.13    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.95/2.13  thf('36', plain,
% 1.95/2.13      (![X14 : $i, X15 : $i]:
% 1.95/2.13         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 1.95/2.13      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.95/2.13  thf(t12_setfam_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.95/2.13  thf('37', plain,
% 1.95/2.13      (![X25 : $i, X26 : $i]:
% 1.95/2.13         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.95/2.13      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.95/2.13  thf('38', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.95/2.13      inference('sup+', [status(thm)], ['36', '37'])).
% 1.95/2.13  thf('39', plain,
% 1.95/2.13      (![X25 : $i, X26 : $i]:
% 1.95/2.13         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 1.95/2.13      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.95/2.13  thf('40', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.95/2.13      inference('sup+', [status(thm)], ['38', '39'])).
% 1.95/2.13  thf(t43_funct_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.95/2.13       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.95/2.13  thf('41', plain,
% 1.95/2.13      (![X56 : $i, X57 : $i]:
% 1.95/2.13         ((k5_relat_1 @ (k6_relat_1 @ X57) @ (k6_relat_1 @ X56))
% 1.95/2.13           = (k6_relat_1 @ (k3_xboole_0 @ X56 @ X57)))),
% 1.95/2.13      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.95/2.13  thf(t182_relat_1, axiom,
% 1.95/2.13    (![A:$i]:
% 1.95/2.13     ( ( v1_relat_1 @ A ) =>
% 1.95/2.13       ( ![B:$i]:
% 1.95/2.13         ( ( v1_relat_1 @ B ) =>
% 1.95/2.13           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.95/2.13             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.95/2.13  thf('42', plain,
% 1.95/2.13      (![X35 : $i, X36 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X35)
% 1.95/2.13          | ((k1_relat_1 @ (k5_relat_1 @ X36 @ X35))
% 1.95/2.13              = (k10_relat_1 @ X36 @ (k1_relat_1 @ X35)))
% 1.95/2.13          | ~ (v1_relat_1 @ X36))),
% 1.95/2.13      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.95/2.13  thf('43', plain,
% 1.95/2.13      (![X30 : $i, X31 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 1.95/2.13          | ~ (v1_relat_1 @ X30))),
% 1.95/2.13      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.95/2.13  thf('44', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.95/2.13           (k1_relat_1 @ X1))
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1))),
% 1.95/2.13      inference('sup+', [status(thm)], ['42', '43'])).
% 1.95/2.13  thf('45', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.95/2.13             (k1_relat_1 @ X1)))),
% 1.95/2.13      inference('simplify', [status(thm)], ['44'])).
% 1.95/2.13  thf('46', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.95/2.13           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.95/2.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.95/2.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.95/2.13      inference('sup+', [status(thm)], ['41', '45'])).
% 1.95/2.13  thf('47', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 1.95/2.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.95/2.13  thf('48', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 1.95/2.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.95/2.13  thf(fc4_funct_1, axiom,
% 1.95/2.13    (![A:$i]:
% 1.95/2.13     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.95/2.13       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.95/2.13  thf('49', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 1.95/2.13      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.95/2.13  thf('50', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 1.95/2.13      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.95/2.13  thf('51', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.95/2.13      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 1.95/2.13  thf('52', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.95/2.13      inference('sup+', [status(thm)], ['40', '51'])).
% 1.95/2.13  thf('53', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (v1_funct_1 @ X1))),
% 1.95/2.13      inference('sup+', [status(thm)], ['35', '52'])).
% 1.95/2.13  thf('54', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1)
% 1.95/2.13          | ~ (v1_funct_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('simplify', [status(thm)], ['33'])).
% 1.95/2.13  thf('55', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 1.95/2.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.95/2.13  thf('56', plain,
% 1.95/2.13      (![X8 : $i, X10 : $i]:
% 1.95/2.13         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.95/2.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.13  thf('57', plain,
% 1.95/2.13      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['55', '56'])).
% 1.95/2.13  thf('58', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_funct_1 @ X0)
% 1.95/2.13          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['54', '57'])).
% 1.95/2.13  thf(t146_relat_1, axiom,
% 1.95/2.13    (![A:$i]:
% 1.95/2.13     ( ( v1_relat_1 @ A ) =>
% 1.95/2.13       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.95/2.13  thf('59', plain,
% 1.95/2.13      (![X27 : $i]:
% 1.95/2.13         (((k9_relat_1 @ X27 @ (k1_relat_1 @ X27)) = (k2_relat_1 @ X27))
% 1.95/2.13          | ~ (v1_relat_1 @ X27))),
% 1.95/2.13      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.95/2.13  thf('60', plain,
% 1.95/2.13      (![X27 : $i]:
% 1.95/2.13         (((k9_relat_1 @ X27 @ (k1_relat_1 @ X27)) = (k2_relat_1 @ X27))
% 1.95/2.13          | ~ (v1_relat_1 @ X27))),
% 1.95/2.13      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.95/2.13  thf('61', plain,
% 1.95/2.13      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.95/2.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.13  thf('62', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.95/2.13      inference('simplify', [status(thm)], ['61'])).
% 1.95/2.13  thf('63', plain,
% 1.95/2.13      (![X47 : $i, X48 : $i]:
% 1.95/2.13         (~ (r1_tarski @ X47 @ (k1_relat_1 @ X48))
% 1.95/2.13          | (r1_tarski @ X47 @ (k10_relat_1 @ X48 @ (k9_relat_1 @ X48 @ X47)))
% 1.95/2.13          | ~ (v1_relat_1 @ X48))),
% 1.95/2.13      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.95/2.13  thf('64', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.95/2.13             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 1.95/2.13      inference('sup-', [status(thm)], ['62', '63'])).
% 1.95/2.13  thf('65', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.95/2.13           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.95/2.13          | ~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('sup+', [status(thm)], ['60', '64'])).
% 1.95/2.13  thf('66', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.95/2.13             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.95/2.13      inference('simplify', [status(thm)], ['65'])).
% 1.95/2.13  thf('67', plain,
% 1.95/2.13      (![X30 : $i, X31 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 1.95/2.13          | ~ (v1_relat_1 @ X30))),
% 1.95/2.13      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.95/2.13  thf('68', plain,
% 1.95/2.13      (![X8 : $i, X10 : $i]:
% 1.95/2.13         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.95/2.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.13  thf('69', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.95/2.13          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['67', '68'])).
% 1.95/2.13  thf('70', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['66', '69'])).
% 1.95/2.13  thf('71', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('simplify', [status(thm)], ['70'])).
% 1.95/2.13  thf('72', plain,
% 1.95/2.13      (![X1 : $i, X3 : $i]:
% 1.95/2.13         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.95/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.95/2.13  thf('73', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('74', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (~ (r2_hidden @ X0 @ X1)
% 1.95/2.13          | (r2_hidden @ X0 @ X2)
% 1.95/2.13          | ~ (r1_tarski @ X1 @ X2))),
% 1.95/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.95/2.13  thf('75', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.95/2.13      inference('sup-', [status(thm)], ['73', '74'])).
% 1.95/2.13  thf('76', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((r1_tarski @ sk_A @ X0)
% 1.95/2.13          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['72', '75'])).
% 1.95/2.13  thf('77', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.95/2.13             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.95/2.13      inference('simplify', [status(thm)], ['65'])).
% 1.95/2.13  thf('78', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (~ (r2_hidden @ X0 @ X1)
% 1.95/2.13          | (r2_hidden @ X0 @ X2)
% 1.95/2.13          | ~ (r1_tarski @ X1 @ X2))),
% 1.95/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.95/2.13  thf('79', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.95/2.13          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['77', '78'])).
% 1.95/2.13  thf('80', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((r1_tarski @ sk_A @ X0)
% 1.95/2.13          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.95/2.13             (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.95/2.13          | ~ (v1_relat_1 @ sk_B))),
% 1.95/2.13      inference('sup-', [status(thm)], ['76', '79'])).
% 1.95/2.13  thf('81', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('82', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((r1_tarski @ sk_A @ X0)
% 1.95/2.13          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.95/2.13             (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.95/2.13      inference('demod', [status(thm)], ['80', '81'])).
% 1.95/2.13  thf('83', plain,
% 1.95/2.13      (![X1 : $i, X3 : $i]:
% 1.95/2.13         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.95/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.95/2.13  thf('84', plain,
% 1.95/2.13      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.95/2.13        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.95/2.13      inference('sup-', [status(thm)], ['82', '83'])).
% 1.95/2.13  thf('85', plain,
% 1.95/2.13      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.95/2.13      inference('simplify', [status(thm)], ['84'])).
% 1.95/2.13  thf(t12_xboole_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.95/2.13  thf('86', plain,
% 1.95/2.13      (![X11 : $i, X12 : $i]:
% 1.95/2.13         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.95/2.13      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.95/2.13  thf('87', plain,
% 1.95/2.13      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.95/2.13         = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['85', '86'])).
% 1.95/2.13  thf('88', plain,
% 1.95/2.13      ((((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 1.95/2.13          = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.95/2.13        | ~ (v1_relat_1 @ sk_B))),
% 1.95/2.13      inference('sup+', [status(thm)], ['71', '87'])).
% 1.95/2.13  thf('89', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('90', plain,
% 1.95/2.13      (![X11 : $i, X12 : $i]:
% 1.95/2.13         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.95/2.13      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.95/2.13  thf('91', plain,
% 1.95/2.13      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.95/2.13      inference('sup-', [status(thm)], ['89', '90'])).
% 1.95/2.13  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('93', plain,
% 1.95/2.13      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.95/2.13      inference('demod', [status(thm)], ['88', '91', '92'])).
% 1.95/2.13  thf('94', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (v1_funct_1 @ X1))),
% 1.95/2.13      inference('sup+', [status(thm)], ['35', '52'])).
% 1.95/2.13  thf('95', plain,
% 1.95/2.13      (![X8 : $i, X10 : $i]:
% 1.95/2.13         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.95/2.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.13  thf('96', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_funct_1 @ X1)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (r1_tarski @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 1.95/2.13          | ((X0) = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 1.95/2.13      inference('sup-', [status(thm)], ['94', '95'])).
% 1.95/2.13  thf('97', plain,
% 1.95/2.13      ((~ (r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 1.95/2.13           (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 1.95/2.13        | ((k2_relat_1 @ sk_B)
% 1.95/2.13            = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))
% 1.95/2.13        | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13        | ~ (v1_funct_1 @ sk_B))),
% 1.95/2.13      inference('sup-', [status(thm)], ['93', '96'])).
% 1.95/2.13  thf('98', plain,
% 1.95/2.13      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.95/2.13      inference('demod', [status(thm)], ['88', '91', '92'])).
% 1.95/2.13  thf('99', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('101', plain,
% 1.95/2.13      ((~ (r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 1.95/2.13           (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 1.95/2.13        | ((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 1.95/2.13      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 1.95/2.13  thf('102', plain,
% 1.95/2.13      ((~ (r1_tarski @ (k2_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B))
% 1.95/2.13        | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13        | ((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 1.95/2.13      inference('sup-', [status(thm)], ['59', '101'])).
% 1.95/2.13  thf('103', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.95/2.13      inference('simplify', [status(thm)], ['61'])).
% 1.95/2.13  thf('104', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('105', plain,
% 1.95/2.13      (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 1.95/2.13      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.95/2.13  thf('106', plain,
% 1.95/2.13      (![X51 : $i, X52 : $i]:
% 1.95/2.13         (((k9_relat_1 @ X52 @ (k10_relat_1 @ X52 @ X51))
% 1.95/2.13            = (k3_xboole_0 @ X51 @ (k9_relat_1 @ X52 @ (k1_relat_1 @ X52))))
% 1.95/2.13          | ~ (v1_funct_1 @ X52)
% 1.95/2.13          | ~ (v1_relat_1 @ X52))),
% 1.95/2.13      inference('cnf', [status(esa)], [t148_funct_1])).
% 1.95/2.13  thf('107', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 1.95/2.13            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 1.95/2.13          | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13          | ~ (v1_funct_1 @ sk_B))),
% 1.95/2.13      inference('sup+', [status(thm)], ['105', '106'])).
% 1.95/2.13  thf('108', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('109', plain, ((v1_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('110', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 1.95/2.13           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 1.95/2.13      inference('demod', [status(thm)], ['107', '108', '109'])).
% 1.95/2.13  thf('111', plain,
% 1.95/2.13      ((((k9_relat_1 @ sk_B @ k1_xboole_0)
% 1.95/2.13          = (k3_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ sk_B)))
% 1.95/2.13        | ~ (v1_funct_1 @ sk_B)
% 1.95/2.13        | ~ (v1_relat_1 @ sk_B))),
% 1.95/2.13      inference('sup+', [status(thm)], ['58', '110'])).
% 1.95/2.13  thf('112', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.95/2.13      inference('sup+', [status(thm)], ['40', '51'])).
% 1.95/2.13  thf('113', plain,
% 1.95/2.13      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['55', '56'])).
% 1.95/2.13  thf('114', plain,
% 1.95/2.13      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['112', '113'])).
% 1.95/2.13  thf('115', plain, ((v1_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('116', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('117', plain, (((k9_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 1.95/2.13      inference('demod', [status(thm)], ['111', '114', '115', '116'])).
% 1.95/2.13  thf(t157_funct_1, axiom,
% 1.95/2.13    (![A:$i,B:$i,C:$i]:
% 1.95/2.13     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.95/2.13       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 1.95/2.13           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 1.95/2.13         ( r1_tarski @ A @ B ) ) ))).
% 1.95/2.13  thf('118', plain,
% 1.95/2.13      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.95/2.13         ((r1_tarski @ X53 @ X54)
% 1.95/2.13          | ~ (v1_relat_1 @ X55)
% 1.95/2.13          | ~ (v1_funct_1 @ X55)
% 1.95/2.13          | ~ (v2_funct_1 @ X55)
% 1.95/2.13          | ~ (r1_tarski @ X53 @ (k1_relat_1 @ X55))
% 1.95/2.13          | ~ (r1_tarski @ (k9_relat_1 @ X55 @ X53) @ (k9_relat_1 @ X55 @ X54)))),
% 1.95/2.13      inference('cnf', [status(esa)], [t157_funct_1])).
% 1.95/2.13  thf('119', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 1.95/2.13          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 1.95/2.13          | ~ (v2_funct_1 @ sk_B)
% 1.95/2.13          | ~ (v1_funct_1 @ sk_B)
% 1.95/2.13          | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13          | (r1_tarski @ X0 @ k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['117', '118'])).
% 1.95/2.13  thf('120', plain, ((v2_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('123', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 1.95/2.13          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 1.95/2.13          | (r1_tarski @ X0 @ k1_xboole_0))),
% 1.95/2.13      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 1.95/2.13  thf('124', plain,
% 1.95/2.13      ((~ (v1_funct_1 @ sk_B)
% 1.95/2.13        | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13        | (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)
% 1.95/2.13        | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ 
% 1.95/2.13             (k1_relat_1 @ sk_B)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['53', '123'])).
% 1.95/2.13  thf('125', plain, ((v1_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('126', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('127', plain,
% 1.95/2.13      (((r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)
% 1.95/2.13        | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ 
% 1.95/2.13             (k1_relat_1 @ sk_B)))),
% 1.95/2.13      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.95/2.13  thf('128', plain,
% 1.95/2.13      ((~ (v1_relat_1 @ sk_B)
% 1.95/2.13        | ~ (v1_funct_1 @ sk_B)
% 1.95/2.13        | (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['34', '127'])).
% 1.95/2.13  thf('129', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('130', plain, ((v1_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('131', plain,
% 1.95/2.13      ((r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)),
% 1.95/2.13      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.95/2.13  thf('132', plain,
% 1.95/2.13      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.95/2.13      inference('sup-', [status(thm)], ['55', '56'])).
% 1.95/2.13  thf('133', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['131', '132'])).
% 1.95/2.13  thf('134', plain,
% 1.95/2.13      (![X35 : $i, X36 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X35)
% 1.95/2.13          | ((k1_relat_1 @ (k5_relat_1 @ X36 @ X35))
% 1.95/2.13              = (k10_relat_1 @ X36 @ (k1_relat_1 @ X35)))
% 1.95/2.13          | ~ (v1_relat_1 @ X36))),
% 1.95/2.13      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.95/2.13  thf(t175_relat_1, axiom,
% 1.95/2.13    (![A:$i,B:$i,C:$i]:
% 1.95/2.13     ( ( v1_relat_1 @ C ) =>
% 1.95/2.13       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.95/2.13         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.95/2.13  thf('135', plain,
% 1.95/2.13      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.95/2.13         (((k10_relat_1 @ X32 @ (k2_xboole_0 @ X33 @ X34))
% 1.95/2.13            = (k2_xboole_0 @ (k10_relat_1 @ X32 @ X33) @ 
% 1.95/2.13               (k10_relat_1 @ X32 @ X34)))
% 1.95/2.13          | ~ (v1_relat_1 @ X32))),
% 1.95/2.13      inference('cnf', [status(esa)], [t175_relat_1])).
% 1.95/2.13  thf('136', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (((k10_relat_1 @ X1 @ (k2_xboole_0 @ X2 @ (k1_relat_1 @ X0)))
% 1.95/2.13            = (k2_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ 
% 1.95/2.13               (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1))),
% 1.95/2.13      inference('sup+', [status(thm)], ['134', '135'])).
% 1.95/2.13  thf('137', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ((k10_relat_1 @ X1 @ (k2_xboole_0 @ X2 @ (k1_relat_1 @ X0)))
% 1.95/2.13              = (k2_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ 
% 1.95/2.13                 (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))))),
% 1.95/2.13      inference('simplify', [status(thm)], ['136'])).
% 1.95/2.13  thf('138', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (((k10_relat_1 @ sk_B @ 
% 1.95/2.13            (k2_xboole_0 @ k1_xboole_0 @ (k1_relat_1 @ X0)))
% 1.95/2.13            = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.95/2.13               (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0))))
% 1.95/2.13          | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('sup+', [status(thm)], ['133', '137'])).
% 1.95/2.13  thf('139', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 1.95/2.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.95/2.13  thf('140', plain,
% 1.95/2.13      (![X11 : $i, X12 : $i]:
% 1.95/2.13         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.95/2.13      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.95/2.13  thf('141', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['139', '140'])).
% 1.95/2.13  thf('142', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['139', '140'])).
% 1.95/2.13  thf('143', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('144', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (((k10_relat_1 @ sk_B @ (k1_relat_1 @ X0))
% 1.95/2.13            = (k1_relat_1 @ (k5_relat_1 @ sk_B @ X0)))
% 1.95/2.13          | ~ (v1_relat_1 @ X0))),
% 1.95/2.13      inference('demod', [status(thm)], ['138', '141', '142', '143'])).
% 1.95/2.13  thf('145', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (((k10_relat_1 @ sk_B @ X0)
% 1.95/2.13            = (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ X0))))
% 1.95/2.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.95/2.13      inference('sup+', [status(thm)], ['9', '144'])).
% 1.95/2.13  thf('146', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 1.95/2.13      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.95/2.13  thf('147', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((k10_relat_1 @ sk_B @ X0)
% 1.95/2.13           = (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ X0))))),
% 1.95/2.13      inference('demod', [status(thm)], ['145', '146'])).
% 1.95/2.13  thf('148', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_relat_1 @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.95/2.13             (k1_relat_1 @ X1)))),
% 1.95/2.13      inference('simplify', [status(thm)], ['44'])).
% 1.95/2.13  thf('149', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 1.95/2.13          | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.95/2.13      inference('sup+', [status(thm)], ['147', '148'])).
% 1.95/2.13  thf('150', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('151', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 1.95/2.13      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.95/2.13  thf('152', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 1.95/2.13      inference('demod', [status(thm)], ['149', '150', '151'])).
% 1.95/2.13  thf('153', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (v1_funct_1 @ X1))),
% 1.95/2.13      inference('sup+', [status(thm)], ['35', '52'])).
% 1.95/2.13  thf('154', plain,
% 1.95/2.13      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.95/2.13         ((r1_tarski @ X53 @ X54)
% 1.95/2.13          | ~ (v1_relat_1 @ X55)
% 1.95/2.13          | ~ (v1_funct_1 @ X55)
% 1.95/2.13          | ~ (v2_funct_1 @ X55)
% 1.95/2.13          | ~ (r1_tarski @ X53 @ (k1_relat_1 @ X55))
% 1.95/2.13          | ~ (r1_tarski @ (k9_relat_1 @ X55 @ X53) @ (k9_relat_1 @ X55 @ X54)))),
% 1.95/2.13      inference('cnf', [status(esa)], [t157_funct_1])).
% 1.95/2.13  thf('155', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_funct_1 @ X1)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 1.95/2.13               (k1_relat_1 @ X1))
% 1.95/2.13          | ~ (v2_funct_1 @ X1)
% 1.95/2.13          | ~ (v1_funct_1 @ X1)
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['153', '154'])).
% 1.95/2.13  thf('156', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 1.95/2.13          | ~ (v2_funct_1 @ X1)
% 1.95/2.13          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 1.95/2.13               (k1_relat_1 @ X1))
% 1.95/2.13          | ~ (v1_relat_1 @ X1)
% 1.95/2.13          | ~ (v1_funct_1 @ X1))),
% 1.95/2.13      inference('simplify', [status(thm)], ['155'])).
% 1.95/2.13  thf('157', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v1_funct_1 @ sk_B)
% 1.95/2.13          | ~ (v1_relat_1 @ sk_B)
% 1.95/2.13          | ~ (v2_funct_1 @ sk_B)
% 1.95/2.13          | (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) @ X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['152', '156'])).
% 1.95/2.13  thf('158', plain, ((v1_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('159', plain, ((v1_relat_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('160', plain, ((v2_funct_1 @ sk_B)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('161', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) @ X0)),
% 1.95/2.13      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 1.95/2.13  thf('162', plain, ($false), inference('demod', [status(thm)], ['8', '161'])).
% 1.95/2.13  
% 1.95/2.13  % SZS output end Refutation
% 1.95/2.13  
% 1.95/2.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
