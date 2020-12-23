%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ojY5MQke5k

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 117 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  674 ( 981 expanded)
%              Number of equality atoms :   42 (  71 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

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

thf('6',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k10_relat_1 @ X42 @ X40 ) @ ( k10_relat_1 @ X42 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
      = ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
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

thf('16',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X48
       != ( k10_relat_1 @ X47 @ X46 ) )
      | ( r2_hidden @ X49 @ ( k1_relat_1 @ X47 ) )
      | ~ ( r2_hidden @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('17',plain,(
    ! [X46: $i,X47: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k10_relat_1 @ X47 @ X46 ) )
      | ( r2_hidden @ X49 @ ( k1_relat_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X52: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
    = ( k10_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('30',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r1_tarski @ X56 @ ( k2_relat_1 @ X57 ) )
      | ( ( k9_relat_1 @ X57 @ ( k10_relat_1 @ X57 @ X56 ) )
        = X56 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k9_relat_1 @ X59 @ ( k10_relat_1 @ X59 @ X58 ) )
        = ( k3_xboole_0 @ X58 @ ( k9_relat_1 @ X59 @ ( k1_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('42',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('43',plain,(
    ! [X52: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X52: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','45','46','47','48'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('50',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X54 @ X53 ) @ X55 )
        = ( k3_xboole_0 @ X53 @ ( k10_relat_1 @ X54 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('51',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ojY5MQke5k
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 152 iterations in 0.082s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(t71_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.53  thf('0', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf(t169_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X39 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.21/0.53          | ~ (v1_relat_1 @ X39))),
% 0.21/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.21/0.53            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf(fc3_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('4', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.53  thf(t175_funct_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.53           ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.53             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53          ( ![B:$i,C:$i]:
% 0.21/0.53            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.53              ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.53                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.21/0.53  thf('6', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t178_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.53         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X40 @ X41)
% 0.21/0.53          | ~ (v1_relat_1 @ X42)
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ X42 @ X40) @ (k10_relat_1 @ X42 @ X41)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.21/0.53           (k10_relat_1 @ X0 @ sk_B))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.53         (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))
% 0.21/0.53        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.53  thf('10', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.53        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X4 : $i, X6 : $i]:
% 0.21/0.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((~ (r1_tarski @ 
% 0.21/0.53           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B) @ 
% 0.21/0.53           (k10_relat_1 @ sk_A @ sk_C_1))
% 0.21/0.53        | ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.21/0.53            = (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf(d13_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.21/0.53           ( ![D:$i]:
% 0.21/0.53             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.53                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.21/0.53         (((X48) != (k10_relat_1 @ X47 @ X46))
% 0.21/0.53          | (r2_hidden @ X49 @ (k1_relat_1 @ X47))
% 0.21/0.53          | ~ (r2_hidden @ X49 @ X48)
% 0.21/0.53          | ~ (v1_funct_1 @ X47)
% 0.21/0.53          | ~ (v1_relat_1 @ X47))),
% 0.21/0.53      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X46 : $i, X47 : $i, X49 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X47)
% 0.21/0.53          | ~ (v1_funct_1 @ X47)
% 0.21/0.53          | ~ (r2_hidden @ X49 @ (k10_relat_1 @ X47 @ X46))
% 0.21/0.53          | (r2_hidden @ X49 @ (k1_relat_1 @ X47)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.21/0.53             (k1_relat_1 @ X1))
% 0.21/0.53          | ~ (v1_funct_1 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['14', '21'])).
% 0.21/0.53  thf('23', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('24', plain, (![X52 : $i]: (v1_funct_1 @ (k6_relat_1 @ X52))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.21/0.53         = (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X39 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.21/0.53          | ~ (v1_relat_1 @ X39))),
% 0.21/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('29', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.53  thf(t147_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.53         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X56 : $i, X57 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X56 @ (k2_relat_1 @ X57))
% 0.21/0.53          | ((k9_relat_1 @ X57 @ (k10_relat_1 @ X57 @ X56)) = (X56))
% 0.21/0.53          | ~ (v1_funct_1 @ X57)
% 0.21/0.53          | ~ (v1_relat_1 @ X57))),
% 0.21/0.53      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.21/0.53              = (k2_relat_1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['27', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.53  thf(t148_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.21/0.53         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X58 : $i, X59 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X59 @ (k10_relat_1 @ X59 @ X58))
% 0.21/0.53            = (k3_xboole_0 @ X58 @ (k9_relat_1 @ X59 @ (k1_relat_1 @ X59))))
% 0.21/0.53          | ~ (v1_funct_1 @ X59)
% 0.21/0.53          | ~ (v1_relat_1 @ X59))),
% 0.21/0.53      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.21/0.53            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.21/0.53              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.21/0.53          (k10_relat_1 @ sk_A @ sk_C_1))
% 0.21/0.53          = (k3_xboole_0 @ sk_B @ 
% 0.21/0.53             (k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))))
% 0.21/0.53        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.21/0.53        | ~ (v1_funct_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['26', '36'])).
% 0.21/0.53  thf('38', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.21/0.53              = (k2_relat_1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.21/0.53            (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.21/0.53            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.53          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.53  thf('42', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('43', plain, (![X52 : $i]: (v1_funct_1 @ (k6_relat_1 @ X52))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('44', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.21/0.53  thf('46', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('47', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('48', plain, (![X52 : $i]: (v1_funct_1 @ (k6_relat_1 @ X52))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.21/0.53         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '45', '46', '47', '48'])).
% 0.21/0.53  thf(t139_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.53         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.21/0.53         (((k10_relat_1 @ (k7_relat_1 @ X54 @ X53) @ X55)
% 0.21/0.53            = (k3_xboole_0 @ X53 @ (k10_relat_1 @ X54 @ X55)))
% 0.21/0.53          | ~ (v1_relat_1 @ X54))),
% 0.21/0.53      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.21/0.53         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.21/0.53          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.21/0.53         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['49', '54'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
