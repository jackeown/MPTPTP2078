%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tUoNqgCC9G

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:42 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 141 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  743 (1189 expanded)
%              Number of equality atoms :   45 (  88 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ ( k1_relat_1 @ X35 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X35 @ X34 ) @ X36 )
      | ( r1_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k2_relat_1 @ X31 ) )
      | ( ( k9_relat_1 @ X31 @ ( k10_relat_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( ( k10_relat_1 @ X14 @ ( k2_relat_1 @ X14 ) )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','21','22','23','24'])).

thf('26',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
      = ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X20
       != ( k10_relat_1 @ X19 @ X18 ) )
      | ( r2_hidden @ X21 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k10_relat_1 @ X19 @ X18 ) )
      | ( r2_hidden @ X21 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
    = ( k10_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','40'])).

thf('42',plain,(
    ! [X14: $i] :
      ( ( ( k10_relat_1 @ X14 @ ( k2_relat_1 @ X14 ) )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('43',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('44',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k2_relat_1 @ X31 ) )
      | ( ( k9_relat_1 @ X31 @ ( k10_relat_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k9_relat_1 @ X33 @ ( k10_relat_1 @ X33 @ X32 ) )
        = ( k3_xboole_0 @ X32 @ ( k9_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('54',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('58',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tUoNqgCC9G
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 895 iterations in 0.668s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.90/1.13  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.13  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.90/1.13  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.90/1.13  thf(t175_funct_2, conjecture,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ![B:$i,C:$i]:
% 0.90/1.13         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.90/1.13           ( ( k10_relat_1 @ A @ C ) =
% 0.90/1.13             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i]:
% 0.90/1.13        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13          ( ![B:$i,C:$i]:
% 0.90/1.13            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.90/1.13              ( ( k10_relat_1 @ A @ C ) =
% 0.90/1.13                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.90/1.13  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t71_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.90/1.13       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.13  thf('1', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.13  thf(d10_xboole_0, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.90/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.13  thf('3', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.90/1.13      inference('simplify', [status(thm)], ['2'])).
% 0.90/1.13  thf(t163_funct_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.13       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.90/1.13           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.90/1.13         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.13         (~ (r1_tarski @ X34 @ (k1_relat_1 @ X35))
% 0.90/1.13          | ~ (r1_tarski @ (k9_relat_1 @ X35 @ X34) @ X36)
% 0.90/1.13          | (r1_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))
% 0.90/1.13          | ~ (v1_funct_1 @ X35)
% 0.90/1.13          | ~ (v1_relat_1 @ X35))),
% 0.90/1.13      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.90/1.13          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.90/1.13      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.90/1.13          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.90/1.13             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.90/1.13          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['1', '5'])).
% 0.90/1.13  thf('7', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.90/1.13      inference('simplify', [status(thm)], ['2'])).
% 0.90/1.13  thf('8', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.13  thf(t147_funct_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.13       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.90/1.13         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (![X30 : $i, X31 : $i]:
% 0.90/1.13         (~ (r1_tarski @ X30 @ (k2_relat_1 @ X31))
% 0.90/1.13          | ((k9_relat_1 @ X31 @ (k10_relat_1 @ X31 @ X30)) = (X30))
% 0.90/1.13          | ~ (v1_funct_1 @ X31)
% 0.90/1.13          | ~ (v1_relat_1 @ X31))),
% 0.90/1.13      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (r1_tarski @ X1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.90/1.13          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.90/1.13              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.13  thf(fc3_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.90/1.13       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.90/1.13  thf('11', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('12', plain, (![X24 : $i]: (v1_funct_1 @ (k6_relat_1 @ X24))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (r1_tarski @ X1 @ X0)
% 0.90/1.13          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.90/1.13              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.90/1.13           (k10_relat_1 @ (k6_relat_1 @ X0) @ X0)) = (X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['7', '13'])).
% 0.90/1.13  thf('15', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.13  thf(t169_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ A ) =>
% 0.90/1.13       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      (![X14 : $i]:
% 0.90/1.13         (((k10_relat_1 @ X14 @ (k2_relat_1 @ X14)) = (k1_relat_1 @ X14))
% 0.90/1.13          | ~ (v1_relat_1 @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.90/1.13            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.90/1.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['15', '16'])).
% 0.90/1.13  thf('18', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.13  thf('19', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('20', plain,
% 0.90/1.13      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '20'])).
% 0.90/1.13  thf('22', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.13  thf('23', plain, (![X24 : $i]: (v1_funct_1 @ (k6_relat_1 @ X24))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('24', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (r1_tarski @ X0 @ X1)
% 0.90/1.13          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['6', '21', '22', '23', '24'])).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.90/1.13        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))),
% 0.90/1.13      inference('sup-', [status(thm)], ['0', '25'])).
% 0.90/1.13  thf('27', plain,
% 0.90/1.13      (![X4 : $i, X6 : $i]:
% 0.90/1.13         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.90/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      ((~ (r1_tarski @ 
% 0.90/1.13           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B) @ 
% 0.90/1.13           (k10_relat_1 @ sk_A @ sk_C_1))
% 0.90/1.13        | ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.90/1.13            = (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.13  thf('29', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.13  thf(d3_tarski, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.13       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.13  thf('30', plain,
% 0.90/1.13      (![X1 : $i, X3 : $i]:
% 0.90/1.13         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.13  thf(d13_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ![B:$i,C:$i]:
% 0.90/1.13         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.90/1.13           ( ![D:$i]:
% 0.90/1.13             ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.13               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.90/1.13                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.90/1.13  thf('31', plain,
% 0.90/1.13      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.90/1.13         (((X20) != (k10_relat_1 @ X19 @ X18))
% 0.90/1.13          | (r2_hidden @ X21 @ (k1_relat_1 @ X19))
% 0.90/1.13          | ~ (r2_hidden @ X21 @ X20)
% 0.90/1.13          | ~ (v1_funct_1 @ X19)
% 0.90/1.13          | ~ (v1_relat_1 @ X19))),
% 0.90/1.13      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X19)
% 0.90/1.13          | ~ (v1_funct_1 @ X19)
% 0.90/1.13          | ~ (r2_hidden @ X21 @ (k10_relat_1 @ X19 @ X18))
% 0.90/1.13          | (r2_hidden @ X21 @ (k1_relat_1 @ X19)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['31'])).
% 0.90/1.13  thf('33', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.90/1.13          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.90/1.13             (k1_relat_1 @ X1))
% 0.90/1.13          | ~ (v1_funct_1 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ X1))),
% 0.90/1.13      inference('sup-', [status(thm)], ['30', '32'])).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      (![X1 : $i, X3 : $i]:
% 0.90/1.13         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.13  thf('35', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.90/1.13          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.13  thf('36', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['35'])).
% 0.90/1.13  thf('37', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['29', '36'])).
% 0.90/1.13  thf('38', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('39', plain, (![X24 : $i]: (v1_funct_1 @ (k6_relat_1 @ X24))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('40', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.90/1.13      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.90/1.13         = (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.90/1.13      inference('demod', [status(thm)], ['28', '40'])).
% 0.90/1.13  thf('42', plain,
% 0.90/1.13      (![X14 : $i]:
% 0.90/1.13         (((k10_relat_1 @ X14 @ (k2_relat_1 @ X14)) = (k1_relat_1 @ X14))
% 0.90/1.13          | ~ (v1_relat_1 @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.90/1.13  thf('43', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.90/1.13      inference('simplify', [status(thm)], ['2'])).
% 0.90/1.13  thf('44', plain,
% 0.90/1.13      (![X30 : $i, X31 : $i]:
% 0.90/1.13         (~ (r1_tarski @ X30 @ (k2_relat_1 @ X31))
% 0.90/1.13          | ((k9_relat_1 @ X31 @ (k10_relat_1 @ X31 @ X30)) = (X30))
% 0.90/1.13          | ~ (v1_funct_1 @ X31)
% 0.90/1.13          | ~ (v1_relat_1 @ X31))),
% 0.90/1.13      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.90/1.13  thf('45', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.90/1.13              = (k2_relat_1 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['42', '45'])).
% 0.90/1.13  thf('47', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['46'])).
% 0.90/1.13  thf(t148_funct_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.13       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.90/1.13         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      (![X32 : $i, X33 : $i]:
% 0.90/1.13         (((k9_relat_1 @ X33 @ (k10_relat_1 @ X33 @ X32))
% 0.90/1.13            = (k3_xboole_0 @ X32 @ (k9_relat_1 @ X33 @ (k1_relat_1 @ X33))))
% 0.90/1.13          | ~ (v1_funct_1 @ X33)
% 0.90/1.13          | ~ (v1_relat_1 @ X33))),
% 0.90/1.13      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.90/1.13            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['47', '48'])).
% 0.90/1.13  thf('50', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.90/1.13              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.90/1.13      inference('simplify', [status(thm)], ['49'])).
% 0.90/1.13  thf('51', plain,
% 0.90/1.13      ((((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.90/1.13          (k10_relat_1 @ sk_A @ sk_C_1))
% 0.90/1.13          = (k3_xboole_0 @ sk_B @ 
% 0.90/1.13             (k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))))
% 0.90/1.13        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.90/1.13        | ~ (v1_funct_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1))))),
% 0.90/1.13      inference('sup+', [status(thm)], ['41', '50'])).
% 0.90/1.13  thf('52', plain,
% 0.90/1.13      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '20'])).
% 0.90/1.13  thf('53', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.90/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.13  thf('54', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('55', plain, (![X24 : $i]: (v1_funct_1 @ (k6_relat_1 @ X24))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.13  thf('56', plain,
% 0.90/1.13      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.90/1.13         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.90/1.13  thf(t139_funct_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ C ) =>
% 0.90/1.13       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.90/1.13         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.90/1.13  thf('57', plain,
% 0.90/1.13      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.13         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.90/1.13            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.90/1.13          | ~ (v1_relat_1 @ X26))),
% 0.90/1.13      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.90/1.13  thf('58', plain,
% 0.90/1.13      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.90/1.13         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('59', plain,
% 0.90/1.13      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.90/1.13          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.13  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('61', plain,
% 0.90/1.13      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.90/1.13         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['59', '60'])).
% 0.90/1.13  thf('62', plain, ($false),
% 0.90/1.13      inference('simplify_reflect-', [status(thm)], ['56', '61'])).
% 0.90/1.13  
% 0.90/1.13  % SZS output end Refutation
% 0.90/1.13  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
