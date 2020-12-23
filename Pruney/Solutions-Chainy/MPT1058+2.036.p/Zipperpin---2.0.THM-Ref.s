%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t6DdhYC86u

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:42 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 160 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  682 (1305 expanded)
%              Number of equality atoms :   42 ( 107 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
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
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( r1_tarski @ X61 @ ( k1_relat_1 @ X62 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X62 @ X61 ) @ X63 )
      | ( r1_tarski @ X61 @ ( k10_relat_1 @ X62 @ X63 ) )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
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
    ! [X43: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ X57 @ ( k2_relat_1 @ X58 ) )
      | ( ( k9_relat_1 @ X58 @ ( k10_relat_1 @ X58 @ X57 ) )
        = X57 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X43: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X41: $i] :
      ( ( ( k10_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X43: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X51: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','17','18','19','20'])).

thf('22',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X51: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
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
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( X47
       != ( k10_relat_1 @ X46 @ X45 ) )
      | ( r2_hidden @ X48 @ ( k1_relat_1 @ X46 ) )
      | ~ ( r2_hidden @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('32',plain,(
    ! [X45: $i,X46: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( r2_hidden @ X48 @ ( k10_relat_1 @ X46 @ X45 ) )
      | ( r2_hidden @ X48 @ ( k1_relat_1 @ X46 ) ) ) ),
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
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X51: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X51 ) ) ),
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
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('43',plain,(
    ! [X59: $i,X60: $i] :
      ( ( ( k9_relat_1 @ X60 @ ( k10_relat_1 @ X60 @ X59 ) )
        = ( k3_xboole_0 @ X59 @ ( k9_relat_1 @ X60 @ ( k1_relat_1 @ X60 ) ) ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X51: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','17','18','19','20'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','17','18','19','20'])).

thf('52',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('53',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X53 @ X52 ) @ X54 )
        = ( k3_xboole_0 @ X52 @ ( k10_relat_1 @ X53 @ X54 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('54',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t6DdhYC86u
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:55:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.37/1.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.59  % Solved by: fo/fo7.sh
% 1.37/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.59  % done 1808 iterations in 1.138s
% 1.37/1.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.59  % SZS output start Refutation
% 1.37/1.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.37/1.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.37/1.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.37/1.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.37/1.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.37/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.37/1.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.37/1.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.37/1.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.59  thf(t175_funct_2, conjecture,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.59       ( ![B:$i,C:$i]:
% 1.37/1.59         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 1.37/1.59           ( ( k10_relat_1 @ A @ C ) =
% 1.37/1.59             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 1.37/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.59    (~( ![A:$i]:
% 1.37/1.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.59          ( ![B:$i,C:$i]:
% 1.37/1.59            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 1.37/1.59              ( ( k10_relat_1 @ A @ C ) =
% 1.37/1.59                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 1.37/1.59    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 1.37/1.59  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf(t71_relat_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.37/1.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.37/1.59  thf('1', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf(d10_xboole_0, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.37/1.59  thf('2', plain,
% 1.37/1.59      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.37/1.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.59  thf('3', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.37/1.59      inference('simplify', [status(thm)], ['2'])).
% 1.37/1.59  thf(t163_funct_1, axiom,
% 1.37/1.59    (![A:$i,B:$i,C:$i]:
% 1.37/1.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.37/1.59       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.37/1.59           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.37/1.59         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.37/1.59  thf('4', plain,
% 1.37/1.59      (![X61 : $i, X62 : $i, X63 : $i]:
% 1.37/1.59         (~ (r1_tarski @ X61 @ (k1_relat_1 @ X62))
% 1.37/1.59          | ~ (r1_tarski @ (k9_relat_1 @ X62 @ X61) @ X63)
% 1.37/1.59          | (r1_tarski @ X61 @ (k10_relat_1 @ X62 @ X63))
% 1.37/1.59          | ~ (v1_funct_1 @ X62)
% 1.37/1.59          | ~ (v1_relat_1 @ X62))),
% 1.37/1.59      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.37/1.59  thf('5', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X0)
% 1.37/1.59          | ~ (v1_funct_1 @ X0)
% 1.37/1.59          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.37/1.59          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 1.37/1.59      inference('sup-', [status(thm)], ['3', '4'])).
% 1.37/1.59  thf('6', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 1.37/1.59          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 1.37/1.59             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.37/1.59          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['1', '5'])).
% 1.37/1.59  thf('7', plain, (![X43 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf('8', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.37/1.59      inference('simplify', [status(thm)], ['2'])).
% 1.37/1.59  thf(t147_funct_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.59       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.37/1.59         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.37/1.59  thf('9', plain,
% 1.37/1.59      (![X57 : $i, X58 : $i]:
% 1.37/1.59         (~ (r1_tarski @ X57 @ (k2_relat_1 @ X58))
% 1.37/1.59          | ((k9_relat_1 @ X58 @ (k10_relat_1 @ X58 @ X57)) = (X57))
% 1.37/1.59          | ~ (v1_funct_1 @ X58)
% 1.37/1.59          | ~ (v1_relat_1 @ X58))),
% 1.37/1.59      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.37/1.59  thf('10', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X0)
% 1.37/1.59          | ~ (v1_funct_1 @ X0)
% 1.37/1.59          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.37/1.59              = (k2_relat_1 @ X0)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['8', '9'])).
% 1.37/1.59  thf('11', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59            (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 1.37/1.59            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 1.37/1.59          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['7', '10'])).
% 1.37/1.59  thf('12', plain, (![X43 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf(t169_relat_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ A ) =>
% 1.37/1.59       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.37/1.59  thf('13', plain,
% 1.37/1.59      (![X41 : $i]:
% 1.37/1.59         (((k10_relat_1 @ X41 @ (k2_relat_1 @ X41)) = (k1_relat_1 @ X41))
% 1.37/1.59          | ~ (v1_relat_1 @ X41))),
% 1.37/1.59      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.37/1.59  thf('14', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 1.37/1.59            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['12', '13'])).
% 1.37/1.59  thf('15', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf(fc3_funct_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.37/1.59       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.37/1.59  thf('16', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('17', plain,
% 1.37/1.59      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.37/1.59      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.37/1.59  thf('18', plain, (![X43 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf('19', plain, (![X51 : $i]: (v1_funct_1 @ (k6_relat_1 @ X51))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('20', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('21', plain,
% 1.37/1.59      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.37/1.59      inference('demod', [status(thm)], ['11', '17', '18', '19', '20'])).
% 1.37/1.59  thf('22', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf('23', plain, (![X51 : $i]: (v1_funct_1 @ (k6_relat_1 @ X51))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('24', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('25', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (r1_tarski @ X0 @ X1)
% 1.37/1.59          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.37/1.59      inference('demod', [status(thm)], ['6', '21', '22', '23', '24'])).
% 1.37/1.59  thf('26', plain,
% 1.37/1.59      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 1.37/1.59        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))),
% 1.37/1.59      inference('sup-', [status(thm)], ['0', '25'])).
% 1.37/1.59  thf('27', plain,
% 1.37/1.59      (![X4 : $i, X6 : $i]:
% 1.37/1.59         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.37/1.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.59  thf('28', plain,
% 1.37/1.59      ((~ (r1_tarski @ 
% 1.37/1.59           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B) @ 
% 1.37/1.59           (k10_relat_1 @ sk_A @ sk_C_1))
% 1.37/1.59        | ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 1.37/1.59            = (k10_relat_1 @ sk_A @ sk_C_1)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['26', '27'])).
% 1.37/1.59  thf('29', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf(d3_tarski, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( r1_tarski @ A @ B ) <=>
% 1.37/1.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.37/1.59  thf('30', plain,
% 1.37/1.59      (![X1 : $i, X3 : $i]:
% 1.37/1.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.37/1.59      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.59  thf(d13_funct_1, axiom,
% 1.37/1.59    (![A:$i]:
% 1.37/1.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.59       ( ![B:$i,C:$i]:
% 1.37/1.59         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 1.37/1.59           ( ![D:$i]:
% 1.37/1.59             ( ( r2_hidden @ D @ C ) <=>
% 1.37/1.59               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 1.37/1.59                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 1.37/1.59  thf('31', plain,
% 1.37/1.59      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.37/1.59         (((X47) != (k10_relat_1 @ X46 @ X45))
% 1.37/1.59          | (r2_hidden @ X48 @ (k1_relat_1 @ X46))
% 1.37/1.59          | ~ (r2_hidden @ X48 @ X47)
% 1.37/1.59          | ~ (v1_funct_1 @ X46)
% 1.37/1.59          | ~ (v1_relat_1 @ X46))),
% 1.37/1.59      inference('cnf', [status(esa)], [d13_funct_1])).
% 1.37/1.59  thf('32', plain,
% 1.37/1.59      (![X45 : $i, X46 : $i, X48 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X46)
% 1.37/1.59          | ~ (v1_funct_1 @ X46)
% 1.37/1.59          | ~ (r2_hidden @ X48 @ (k10_relat_1 @ X46 @ X45))
% 1.37/1.59          | (r2_hidden @ X48 @ (k1_relat_1 @ X46)))),
% 1.37/1.59      inference('simplify', [status(thm)], ['31'])).
% 1.37/1.59  thf('33', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.59         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 1.37/1.59          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.37/1.59             (k1_relat_1 @ X1))
% 1.37/1.59          | ~ (v1_funct_1 @ X1)
% 1.37/1.59          | ~ (v1_relat_1 @ X1))),
% 1.37/1.59      inference('sup-', [status(thm)], ['30', '32'])).
% 1.37/1.59  thf('34', plain,
% 1.37/1.59      (![X1 : $i, X3 : $i]:
% 1.37/1.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.37/1.59      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.59  thf('35', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (~ (v1_relat_1 @ X0)
% 1.37/1.59          | ~ (v1_funct_1 @ X0)
% 1.37/1.59          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.37/1.59          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.59  thf('36', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_funct_1 @ X0)
% 1.37/1.59          | ~ (v1_relat_1 @ X0))),
% 1.37/1.59      inference('simplify', [status(thm)], ['35'])).
% 1.37/1.59  thf('37', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['29', '36'])).
% 1.37/1.59  thf('38', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('39', plain, (![X51 : $i]: (v1_funct_1 @ (k6_relat_1 @ X51))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('40', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 1.37/1.59      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.37/1.59  thf('41', plain,
% 1.37/1.59      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 1.37/1.59         = (k10_relat_1 @ sk_A @ sk_C_1))),
% 1.37/1.59      inference('demod', [status(thm)], ['28', '40'])).
% 1.37/1.59  thf('42', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 1.37/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.37/1.59  thf(t148_funct_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.59       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 1.37/1.59         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 1.37/1.59  thf('43', plain,
% 1.37/1.59      (![X59 : $i, X60 : $i]:
% 1.37/1.59         (((k9_relat_1 @ X60 @ (k10_relat_1 @ X60 @ X59))
% 1.37/1.59            = (k3_xboole_0 @ X59 @ (k9_relat_1 @ X60 @ (k1_relat_1 @ X60))))
% 1.37/1.59          | ~ (v1_funct_1 @ X60)
% 1.37/1.59          | ~ (v1_relat_1 @ X60))),
% 1.37/1.59      inference('cnf', [status(esa)], [t148_funct_1])).
% 1.37/1.59  thf('44', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.37/1.59            = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 1.37/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.37/1.59          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['42', '43'])).
% 1.37/1.59  thf('45', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('46', plain, (![X51 : $i]: (v1_funct_1 @ (k6_relat_1 @ X51))),
% 1.37/1.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.37/1.59  thf('47', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.37/1.59           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 1.37/1.59      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.37/1.59  thf('48', plain,
% 1.37/1.59      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.37/1.59      inference('demod', [status(thm)], ['11', '17', '18', '19', '20'])).
% 1.37/1.59  thf('49', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.37/1.59           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (k3_xboole_0 @ X1 @ X0))),
% 1.37/1.59      inference('demod', [status(thm)], ['47', '48'])).
% 1.37/1.59  thf('50', plain,
% 1.37/1.59      (((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 1.37/1.59         (k10_relat_1 @ sk_A @ sk_C_1))
% 1.37/1.59         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 1.37/1.59      inference('sup+', [status(thm)], ['41', '49'])).
% 1.37/1.59  thf('51', plain,
% 1.37/1.59      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.37/1.59      inference('demod', [status(thm)], ['11', '17', '18', '19', '20'])).
% 1.37/1.59  thf('52', plain,
% 1.37/1.59      (((k10_relat_1 @ sk_A @ sk_C_1)
% 1.37/1.59         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 1.37/1.59      inference('demod', [status(thm)], ['50', '51'])).
% 1.37/1.59  thf(t139_funct_1, axiom,
% 1.37/1.59    (![A:$i,B:$i,C:$i]:
% 1.37/1.59     ( ( v1_relat_1 @ C ) =>
% 1.37/1.59       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.37/1.59         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.37/1.59  thf('53', plain,
% 1.37/1.59      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.37/1.59         (((k10_relat_1 @ (k7_relat_1 @ X53 @ X52) @ X54)
% 1.37/1.59            = (k3_xboole_0 @ X52 @ (k10_relat_1 @ X53 @ X54)))
% 1.37/1.59          | ~ (v1_relat_1 @ X53))),
% 1.37/1.59      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.37/1.59  thf('54', plain,
% 1.37/1.59      (((k10_relat_1 @ sk_A @ sk_C_1)
% 1.37/1.59         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf('55', plain,
% 1.37/1.59      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 1.37/1.59          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 1.37/1.59        | ~ (v1_relat_1 @ sk_A))),
% 1.37/1.59      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.59  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf('57', plain,
% 1.37/1.59      (((k10_relat_1 @ sk_A @ sk_C_1)
% 1.37/1.59         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 1.37/1.59      inference('demod', [status(thm)], ['55', '56'])).
% 1.37/1.59  thf('58', plain, ($false),
% 1.37/1.59      inference('simplify_reflect-', [status(thm)], ['52', '57'])).
% 1.37/1.59  
% 1.37/1.59  % SZS output end Refutation
% 1.37/1.59  
% 1.37/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
