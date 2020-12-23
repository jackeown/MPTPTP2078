%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qhuj5Roo93

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 210 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   24
%              Number of atoms          : 1075 (2448 expanded)
%              Number of equality atoms :   46 ( 118 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k10_relat_1 @ X31 @ X32 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X31 ) @ X32 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k10_relat_1 @ X31 @ X32 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X31 ) @ X32 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( ( k9_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('10',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('11',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k5_relat_1 @ X35 @ ( k2_funct_1 @ X35 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ X33 ) @ ( k1_relat_1 @ X34 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) )
       != ( k1_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k10_relat_1 @ X23 @ X21 ) @ ( k10_relat_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

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

thf('28',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k9_relat_1 @ X29 @ X30 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X29 ) @ X30 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('39',plain,(
    ! [X19: $i] :
      ( ( ( k9_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('40',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('41',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k9_relat_1 @ X29 @ X30 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X29 ) @ X30 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k10_relat_1 @ X23 @ X21 ) @ ( k10_relat_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k9_relat_1 @ X29 @ X30 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X29 ) @ X30 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('61',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('62',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','71','72','73','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['37','75'])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qhuj5Roo93
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 174 iterations in 0.081s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.53  thf(t155_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ B ) =>
% 0.21/0.53         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X31 : $i, X32 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X31)
% 0.21/0.53          | ((k10_relat_1 @ X31 @ X32)
% 0.21/0.53              = (k9_relat_1 @ (k2_funct_1 @ X31) @ X32))
% 0.21/0.53          | ~ (v1_funct_1 @ X31)
% 0.21/0.53          | ~ (v1_relat_1 @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.53  thf(dt_k2_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.53         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X26 : $i]:
% 0.21/0.53         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X26 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X26 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X31 : $i, X32 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X31)
% 0.21/0.53          | ((k10_relat_1 @ X31 @ X32)
% 0.21/0.53              = (k9_relat_1 @ (k2_funct_1 @ X31) @ X32))
% 0.21/0.53          | ~ (v1_funct_1 @ X31)
% 0.21/0.53          | ~ (v1_relat_1 @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.53  thf(t146_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X19 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X19 @ (k1_relat_1 @ X19)) = (k2_relat_1 @ X19))
% 0.21/0.53          | ~ (v1_relat_1 @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.53  thf(t169_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X20 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X20 @ (k2_relat_1 @ X20)) = (k1_relat_1 @ X20))
% 0.21/0.53          | ~ (v1_relat_1 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X26 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X26 : $i]:
% 0.21/0.53         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf(t61_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ A ) =>
% 0.21/0.53         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.21/0.53             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.53           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.21/0.53             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X35 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X35)
% 0.21/0.53          | ((k5_relat_1 @ X35 @ (k2_funct_1 @ X35))
% 0.21/0.53              = (k6_relat_1 @ (k1_relat_1 @ X35)))
% 0.21/0.53          | ~ (v1_funct_1 @ X35)
% 0.21/0.53          | ~ (v1_relat_1 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.53  thf(t27_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.21/0.53             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X33 : $i, X34 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X33)
% 0.21/0.53          | ~ (v1_funct_1 @ X33)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X33) @ (k1_relat_1 @ X34))
% 0.21/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X33 @ X34)) != (k1_relat_1 @ X33))
% 0.21/0.53          | ~ (v1_funct_1 @ X34)
% 0.21/0.53          | ~ (v1_relat_1 @ X34))),
% 0.21/0.53      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))) != (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf(t71_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.53  thf('15', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf(t178_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.53         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X21 @ X22)
% 0.21/0.53          | ~ (v1_relat_1 @ X23)
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ X23 @ X21) @ (k10_relat_1 @ X23 @ X22)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 0.21/0.53             (k10_relat_1 @ X1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.21/0.53          | ~ (v1_relat_1 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.21/0.53           (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['9', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.21/0.53             (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['8', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.53  thf(t164_funct_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.21/0.53         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.21/0.53            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.21/0.53  thf('28', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t1_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.53       ( r1_tarski @ A @ C ) ))).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.53          | ~ (r1_tarski @ X6 @ X7)
% 0.21/0.53          | (r1_tarski @ X5 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.53        | (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.53  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.53  thf(t147_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.53         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.21/0.53          | ((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27)) = (X27))
% 0.21/0.53          | ~ (v1_funct_1 @ X28)
% 0.21/0.53          | ~ (v1_relat_1 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.53            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf(t154_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ B ) =>
% 0.21/0.53         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X29)
% 0.21/0.53          | ((k9_relat_1 @ X29 @ X30)
% 0.21/0.53              = (k10_relat_1 @ (k2_funct_1 @ X29) @ X30))
% 0.21/0.53          | ~ (v1_funct_1 @ X29)
% 0.21/0.53          | ~ (v1_relat_1 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X19 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X19 @ (k1_relat_1 @ X19)) = (k2_relat_1 @ X19))
% 0.21/0.53          | ~ (v1_relat_1 @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X26 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X29)
% 0.21/0.53          | ((k9_relat_1 @ X29 @ X30)
% 0.21/0.53              = (k10_relat_1 @ (k2_funct_1 @ X29) @ X30))
% 0.21/0.53          | ~ (v1_funct_1 @ X29)
% 0.21/0.53          | ~ (v1_relat_1 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.21/0.53  thf('42', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X21 @ X22)
% 0.21/0.53          | ~ (v1_relat_1 @ X23)
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ X23 @ X21) @ (k10_relat_1 @ X23 @ X22)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.21/0.53           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 0.21/0.53           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['41', '44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 0.21/0.53             (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 0.21/0.53           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.21/0.53         (k2_relat_1 @ sk_B))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['39', '47'])).
% 0.21/0.53  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.21/0.53        (k2_relat_1 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.21/0.53          | ((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27)) = (X27))
% 0.21/0.53          | ~ (v1_funct_1 @ X28)
% 0.21/0.53          | ~ (v1_relat_1 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ((k9_relat_1 @ sk_B @ 
% 0.21/0.53            (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.53            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (((k9_relat_1 @ sk_B @ 
% 0.21/0.53         (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.53         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53          = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['38', '58'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X29)
% 0.21/0.53          | ((k9_relat_1 @ X29 @ X30)
% 0.21/0.53              = (k10_relat_1 @ (k2_funct_1 @ X29) @ X30))
% 0.21/0.53          | ~ (v1_funct_1 @ X29)
% 0.21/0.53          | ~ (v1_relat_1 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.21/0.53        (k2_relat_1 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.53  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.21/0.53          | ((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27)) = (X27))
% 0.21/0.53          | ~ (v1_funct_1 @ X28)
% 0.21/0.53          | ~ (v1_relat_1 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ((k9_relat_1 @ sk_B @ 
% 0.21/0.53            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53            = (k9_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.53  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53         = (k9_relat_1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.53  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (((k9_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '71', '72', '73', '74'])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53            = (sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '75'])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53            = (sk_A))
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '76'])).
% 0.21/0.53  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53          = (sk_A))
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53            = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '80'])).
% 0.21/0.53  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53         = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      ((((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '84'])).
% 0.21/0.53  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('87', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('88', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('89', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('91', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
