%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1058+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ltOscVkiAD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 23.97s
% Output     : Refutation 23.97s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  147 ( 219 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_116_type,type,(
    sk_C_116: $i )).

thf(sk_B_99_type,type,(
    sk_B_99: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ ( A @ C ) @ B ) )
         => ( ( k10_relat_1 @ ( A @ C ) )
            = ( k10_relat_1 @ ( k7_relat_1 @ ( A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ ( A @ C ) @ B ) )
           => ( ( k10_relat_1 @ ( A @ C ) )
              = ( k10_relat_1 @ ( k7_relat_1 @ ( A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) @ sk_B_99 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) @ sk_B_99 ) )
    = ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( sk_B_99 @ ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) ) ) )
    = ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ ( C @ A ) @ B ) )
        = ( k3_xboole_0 @ ( A @ ( k10_relat_1 @ ( C @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X2788: $i,X2789: $i,X2790: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( X2789 @ X2788 ) @ X2790 ) )
        = ( k3_xboole_0 @ ( X2788 @ ( k10_relat_1 @ ( X2789 @ X2790 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2789 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('6',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( sk_A_16 @ sk_B_99 ) @ sk_C_116 ) )
      = ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) ) )
    | ~ ( v1_relat_1 @ sk_A_16 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ ( sk_A_16 @ sk_B_99 ) @ sk_C_116 ) )
    = ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k10_relat_1 @ ( sk_A_16 @ sk_C_116 ) )
 != ( k10_relat_1 @ ( k7_relat_1 @ ( sk_A_16 @ sk_B_99 ) @ sk_C_116 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
