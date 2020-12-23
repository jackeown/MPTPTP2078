%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ltkIS5y3X

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:51 EST 2020

% Result     : Theorem 25.50s
% Output     : Refutation 25.50s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  778 (1010 expanded)
%              Number of equality atoms :   43 (  60 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ X39 ) )
      | ( r2_hidden @ X37 @ ( k1_relat_1 @ ( k7_relat_1 @ X39 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X3 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ( X2
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X2
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ ( k7_relat_1 @ X39 @ X38 ) ) )
      | ( r2_hidden @ X37 @ ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ X3 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('23',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ ( k7_relat_1 @ X39 @ X38 ) ) )
      | ( r2_hidden @ X37 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ X2 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['21','25'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('27',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k7_relat_1 @ X41 @ X40 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X40 ) @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t37_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) )
          = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_1])).

thf('28',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
 != ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ltkIS5y3X
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:06:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 25.50/25.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 25.50/25.70  % Solved by: fo/fo7.sh
% 25.50/25.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.50/25.70  % done 8565 iterations in 25.252s
% 25.50/25.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 25.50/25.70  % SZS output start Refutation
% 25.50/25.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 25.50/25.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 25.50/25.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 25.50/25.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 25.50/25.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 25.50/25.70  thf(sk_B_type, type, sk_B: $i).
% 25.50/25.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 25.50/25.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 25.50/25.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 25.50/25.70  thf(sk_A_type, type, sk_A: $i).
% 25.50/25.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 25.50/25.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 25.50/25.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 25.50/25.70  thf(d4_xboole_0, axiom,
% 25.50/25.70    (![A:$i,B:$i,C:$i]:
% 25.50/25.70     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 25.50/25.70       ( ![D:$i]:
% 25.50/25.70         ( ( r2_hidden @ D @ C ) <=>
% 25.50/25.70           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 25.50/25.70  thf('0', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 25.50/25.70  thf(t12_setfam_1, axiom,
% 25.50/25.70    (![A:$i,B:$i]:
% 25.50/25.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 25.50/25.70  thf('1', plain,
% 25.50/25.70      (![X35 : $i, X36 : $i]:
% 25.50/25.70         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 25.50/25.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 25.50/25.70  thf('2', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k1_setfam_1 @ (k2_tarski @ X3 @ X4)))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('demod', [status(thm)], ['0', '1'])).
% 25.50/25.70  thf('3', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 25.50/25.70  thf('4', plain,
% 25.50/25.70      (![X35 : $i, X36 : $i]:
% 25.50/25.70         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 25.50/25.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 25.50/25.70  thf('5', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k1_setfam_1 @ (k2_tarski @ X3 @ X4)))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('demod', [status(thm)], ['3', '4'])).
% 25.50/25.70  thf(t86_relat_1, axiom,
% 25.50/25.70    (![A:$i,B:$i,C:$i]:
% 25.50/25.70     ( ( v1_relat_1 @ C ) =>
% 25.50/25.70       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 25.50/25.70         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 25.50/25.70  thf('6', plain,
% 25.50/25.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 25.50/25.70         (~ (r2_hidden @ X37 @ X38)
% 25.50/25.70          | ~ (r2_hidden @ X37 @ (k1_relat_1 @ X39))
% 25.50/25.70          | (r2_hidden @ X37 @ (k1_relat_1 @ (k7_relat_1 @ X39 @ X38)))
% 25.50/25.70          | ~ (v1_relat_1 @ X39))),
% 25.50/25.70      inference('cnf', [status(esa)], [t86_relat_1])).
% 25.50/25.70  thf('7', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.50/25.70         ((r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X0) @ X1) @ X2)
% 25.50/25.70          | ((X2) = (k1_setfam_1 @ (k2_tarski @ X1 @ (k1_relat_1 @ X0))))
% 25.50/25.70          | ~ (v1_relat_1 @ X0)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X0) @ X1) @ 
% 25.50/25.70             (k1_relat_1 @ (k7_relat_1 @ X0 @ X3)))
% 25.50/25.70          | ~ (r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X0) @ X1) @ X3))),
% 25.50/25.70      inference('sup-', [status(thm)], ['5', '6'])).
% 25.50/25.70  thf('8', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.50/25.70         ((r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 25.50/25.70          | ((X2) = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1))))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X1) @ X0) @ 
% 25.50/25.70             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 25.50/25.70          | ~ (v1_relat_1 @ X1)
% 25.50/25.70          | ((X2) = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1))))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X1) @ X0) @ X2))),
% 25.50/25.70      inference('sup-', [status(thm)], ['2', '7'])).
% 25.50/25.70  thf('9', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.50/25.70         (~ (v1_relat_1 @ X1)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X1) @ X0) @ 
% 25.50/25.70             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 25.50/25.70          | ((X2) = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1))))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X2 @ (k1_relat_1 @ X1) @ X0) @ X2))),
% 25.50/25.70      inference('simplify', [status(thm)], ['8'])).
% 25.50/25.70  thf('10', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i]:
% 25.50/25.70         ((r2_hidden @ 
% 25.50/25.70           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1) @ 
% 25.50/25.70            X0) @ 
% 25.50/25.70           (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1))))
% 25.50/25.70          | ~ (v1_relat_1 @ X1))),
% 25.50/25.70      inference('eq_fact', [status(thm)], ['9'])).
% 25.50/25.70  thf('11', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k1_setfam_1 @ (k2_tarski @ X3 @ X4)))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('demod', [status(thm)], ['3', '4'])).
% 25.50/25.70  thf('12', plain,
% 25.50/25.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 25.50/25.70         (~ (r2_hidden @ X37 @ (k1_relat_1 @ (k7_relat_1 @ X39 @ X38)))
% 25.50/25.70          | (r2_hidden @ X37 @ (k1_relat_1 @ X39))
% 25.50/25.70          | ~ (v1_relat_1 @ X39))),
% 25.50/25.70      inference('cnf', [status(esa)], [t86_relat_1])).
% 25.50/25.70  thf('13', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.50/25.70         ((r2_hidden @ 
% 25.50/25.70           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X3 @ X2) @ X3)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X2 @ X3)))
% 25.50/25.70          | ~ (v1_relat_1 @ X1)
% 25.50/25.70          | (r2_hidden @ 
% 25.50/25.70             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X3 @ X2) @ 
% 25.50/25.70             (k1_relat_1 @ X1)))),
% 25.50/25.70      inference('sup-', [status(thm)], ['11', '12'])).
% 25.50/25.70  thf('14', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.50/25.70         ((r2_hidden @ 
% 25.50/25.70           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)) @ (k1_relat_1 @ X0) @ 
% 25.50/25.70            X1) @ 
% 25.50/25.70           (k1_relat_1 @ X0))
% 25.50/25.70          | ~ (v1_relat_1 @ X0)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ X2))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X1 @ (k1_relat_1 @ X0)))))),
% 25.50/25.70      inference('eq_fact', [status(thm)], ['13'])).
% 25.50/25.70  thf('15', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 25.50/25.70          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 25.50/25.70          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 25.50/25.70          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 25.50/25.70  thf('16', plain,
% 25.50/25.70      (![X35 : $i, X36 : $i]:
% 25.50/25.70         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 25.50/25.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 25.50/25.70  thf('17', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k1_setfam_1 @ (k2_tarski @ X3 @ X4)))
% 25.50/25.70          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 25.50/25.70          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 25.50/25.70          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('demod', [status(thm)], ['15', '16'])).
% 25.50/25.70  thf('18', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.50/25.70         (((k1_relat_1 @ (k7_relat_1 @ X0 @ X2))
% 25.50/25.70            = (k1_setfam_1 @ (k2_tarski @ X1 @ (k1_relat_1 @ X0))))
% 25.50/25.70          | ~ (v1_relat_1 @ X0)
% 25.50/25.70          | ~ (r2_hidden @ 
% 25.50/25.70               (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)) @ 
% 25.50/25.70                (k1_relat_1 @ X0) @ X1) @ 
% 25.50/25.70               (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 25.50/25.70          | ~ (r2_hidden @ 
% 25.50/25.70               (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)) @ 
% 25.50/25.70                (k1_relat_1 @ X0) @ X1) @ 
% 25.50/25.70               X1)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ X2))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X1 @ (k1_relat_1 @ X0)))))),
% 25.50/25.70      inference('sup-', [status(thm)], ['14', '17'])).
% 25.50/25.70  thf('19', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.50/25.70         (~ (r2_hidden @ 
% 25.50/25.70             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)) @ 
% 25.50/25.70              (k1_relat_1 @ X0) @ X1) @ 
% 25.50/25.70             X1)
% 25.50/25.70          | ~ (r2_hidden @ 
% 25.50/25.70               (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)) @ 
% 25.50/25.70                (k1_relat_1 @ X0) @ X1) @ 
% 25.50/25.70               (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 25.50/25.70          | ~ (v1_relat_1 @ X0)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ X2))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X1 @ (k1_relat_1 @ X0)))))),
% 25.50/25.70      inference('simplify', [status(thm)], ['18'])).
% 25.50/25.70  thf('20', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i]:
% 25.50/25.70         (~ (v1_relat_1 @ X1)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1))))
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1))))
% 25.50/25.70          | ~ (v1_relat_1 @ X1)
% 25.50/25.70          | ~ (r2_hidden @ 
% 25.50/25.70               (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 25.50/25.70                (k1_relat_1 @ X1) @ X0) @ 
% 25.50/25.70               X0))),
% 25.50/25.70      inference('sup-', [status(thm)], ['10', '19'])).
% 25.50/25.70  thf('21', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i]:
% 25.50/25.70         (~ (r2_hidden @ 
% 25.50/25.70             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 25.50/25.70              (k1_relat_1 @ X1) @ X0) @ 
% 25.50/25.70             X0)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1))))
% 25.50/25.70          | ~ (v1_relat_1 @ X1))),
% 25.50/25.70      inference('simplify', [status(thm)], ['20'])).
% 25.50/25.70  thf('22', plain,
% 25.50/25.70      (![X3 : $i, X4 : $i, X7 : $i]:
% 25.50/25.70         (((X7) = (k1_setfam_1 @ (k2_tarski @ X3 @ X4)))
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 25.50/25.70          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 25.50/25.70      inference('demod', [status(thm)], ['0', '1'])).
% 25.50/25.70  thf('23', plain,
% 25.50/25.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 25.50/25.70         (~ (r2_hidden @ X37 @ (k1_relat_1 @ (k7_relat_1 @ X39 @ X38)))
% 25.50/25.70          | (r2_hidden @ X37 @ X38)
% 25.50/25.70          | ~ (v1_relat_1 @ X39))),
% 25.50/25.70      inference('cnf', [status(esa)], [t86_relat_1])).
% 25.50/25.70  thf('24', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.50/25.70         ((r2_hidden @ 
% 25.50/25.70           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X3 @ X2) @ X2)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X2 @ X3)))
% 25.50/25.70          | ~ (v1_relat_1 @ X1)
% 25.50/25.70          | (r2_hidden @ 
% 25.50/25.70             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X3 @ X2) @ X0))),
% 25.50/25.70      inference('sup-', [status(thm)], ['22', '23'])).
% 25.50/25.70  thf('25', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.50/25.70         ((r2_hidden @ 
% 25.50/25.70           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X0)) @ X1 @ X0) @ X0)
% 25.50/25.70          | ~ (v1_relat_1 @ X2)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X2 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 25.50/25.70      inference('eq_fact', [status(thm)], ['24'])).
% 25.50/25.70  thf('26', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i]:
% 25.50/25.70         (~ (v1_relat_1 @ X1)
% 25.50/25.70          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 25.50/25.70              = (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ X1)))))),
% 25.50/25.70      inference('clc', [status(thm)], ['21', '25'])).
% 25.50/25.70  thf(t94_relat_1, axiom,
% 25.50/25.70    (![A:$i,B:$i]:
% 25.50/25.70     ( ( v1_relat_1 @ B ) =>
% 25.50/25.70       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 25.50/25.70  thf('27', plain,
% 25.50/25.70      (![X40 : $i, X41 : $i]:
% 25.50/25.70         (((k7_relat_1 @ X41 @ X40) = (k5_relat_1 @ (k6_relat_1 @ X40) @ X41))
% 25.50/25.70          | ~ (v1_relat_1 @ X41))),
% 25.50/25.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 25.50/25.70  thf(t37_funct_1, conjecture,
% 25.50/25.70    (![A:$i,B:$i]:
% 25.50/25.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.50/25.70       ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) =
% 25.50/25.70         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 25.50/25.70  thf(zf_stmt_0, negated_conjecture,
% 25.50/25.70    (~( ![A:$i,B:$i]:
% 25.50/25.70        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.50/25.70          ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) =
% 25.50/25.70            ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 25.50/25.70    inference('cnf.neg', [status(esa)], [t37_funct_1])).
% 25.50/25.70  thf('28', plain,
% 25.50/25.70      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 25.50/25.70         != (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 25.50/25.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.50/25.70  thf(commutativity_k3_xboole_0, axiom,
% 25.50/25.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 25.50/25.70  thf('29', plain,
% 25.50/25.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.50/25.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.50/25.70  thf('30', plain,
% 25.50/25.70      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 25.50/25.70         != (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 25.50/25.70      inference('demod', [status(thm)], ['28', '29'])).
% 25.50/25.70  thf('31', plain,
% 25.50/25.70      (![X35 : $i, X36 : $i]:
% 25.50/25.70         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 25.50/25.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 25.50/25.70  thf('32', plain,
% 25.50/25.70      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 25.50/25.70         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B))))),
% 25.50/25.70      inference('demod', [status(thm)], ['30', '31'])).
% 25.50/25.70  thf('33', plain,
% 25.50/25.70      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 25.50/25.70          != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B))))
% 25.50/25.70        | ~ (v1_relat_1 @ sk_B))),
% 25.50/25.70      inference('sup-', [status(thm)], ['27', '32'])).
% 25.50/25.70  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 25.50/25.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.50/25.70  thf('35', plain,
% 25.50/25.70      (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 25.50/25.70         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B))))),
% 25.50/25.70      inference('demod', [status(thm)], ['33', '34'])).
% 25.50/25.70  thf('36', plain,
% 25.50/25.70      ((((k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B)))
% 25.50/25.70          != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B))))
% 25.50/25.70        | ~ (v1_relat_1 @ sk_B))),
% 25.50/25.70      inference('sup-', [status(thm)], ['26', '35'])).
% 25.50/25.70  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 25.50/25.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.50/25.70  thf('38', plain,
% 25.50/25.70      (((k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B)))
% 25.50/25.70         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B))))),
% 25.50/25.70      inference('demod', [status(thm)], ['36', '37'])).
% 25.50/25.70  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 25.50/25.70  
% 25.50/25.70  % SZS output end Refutation
% 25.50/25.70  
% 25.50/25.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
