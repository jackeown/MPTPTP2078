%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Awc0soFHb0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:42 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 175 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  934 (1500 expanded)
%              Number of equality atoms :   57 ( 109 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X41: $i] :
      ( ( ( k10_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X53: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k10_relat_1 @ X42 @ ( k2_xboole_0 @ X43 @ X44 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X42 @ X43 ) @ ( k10_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['5','15'])).

thf('17',plain,(
    ! [X53: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
      = ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('29',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k10_relat_1 @ X42 @ ( k2_xboole_0 @ X43 @ X44 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X42 @ X43 ) @ ( k10_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X53: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X50
       != ( k10_relat_1 @ X49 @ X48 ) )
      | ( r2_hidden @ X51 @ ( k1_relat_1 @ X49 ) )
      | ~ ( r2_hidden @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('34',plain,(
    ! [X48: $i,X49: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( r2_hidden @ X51 @ ( k10_relat_1 @ X49 @ X48 ) )
      | ( r2_hidden @ X51 @ ( k1_relat_1 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X54: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X53: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
    = ( k10_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','43'])).

thf('45',plain,(
    ! [X41: $i] :
      ( ( ( k10_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('46',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('47',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r1_tarski @ X58 @ ( k2_relat_1 @ X59 ) )
      | ( ( k9_relat_1 @ X59 @ ( k10_relat_1 @ X59 @ X58 ) )
        = X58 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k9_relat_1 @ X61 @ ( k10_relat_1 @ X61 @ X60 ) )
        = ( k3_xboole_0 @ X60 @ ( k9_relat_1 @ X61 @ ( k1_relat_1 @ X61 ) ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('56',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k9_relat_1 @ X61 @ ( k10_relat_1 @ X61 @ X60 ) )
        = ( k3_xboole_0 @ X60 @ ( k9_relat_1 @ X61 @ ( k1_relat_1 @ X61 ) ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X53: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X54: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X54: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('69',plain,(
    ! [X53: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','63','66','67','68','69'])).

thf('71',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,(
    ! [X53: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X54: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('74',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['54','70','71','72','73'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('75',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X56 @ X55 ) @ X57 )
        = ( k3_xboole_0 @ X55 @ ( k10_relat_1 @ X56 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('76',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Awc0soFHb0
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:03:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 684 iterations in 0.426s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.87  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.68/0.87  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.68/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.87  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.68/0.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.68/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.88  thf(t71_relat_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.68/0.88       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.68/0.88  thf('0', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.68/0.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.88  thf(t169_relat_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ A ) =>
% 0.68/0.88       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (![X41 : $i]:
% 0.68/0.88         (((k10_relat_1 @ X41 @ (k2_relat_1 @ X41)) = (k1_relat_1 @ X41))
% 0.68/0.88          | ~ (v1_relat_1 @ X41))),
% 0.68/0.88      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.68/0.88            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.68/0.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['0', '1'])).
% 0.68/0.88  thf('3', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.68/0.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.88  thf(fc3_funct_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.68/0.88       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.68/0.88  thf('4', plain, (![X53 : $i]: (v1_relat_1 @ (k6_relat_1 @ X53))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.68/0.88  thf(d10_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('7', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.68/0.88      inference('simplify', [status(thm)], ['6'])).
% 0.68/0.88  thf(t175_funct_2, conjecture,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88       ( ![B:$i,C:$i]:
% 0.68/0.88         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.68/0.88           ( ( k10_relat_1 @ A @ C ) =
% 0.68/0.88             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i]:
% 0.68/0.88        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88          ( ![B:$i,C:$i]:
% 0.68/0.88            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.68/0.88              ( ( k10_relat_1 @ A @ C ) =
% 0.68/0.88                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.68/0.88  thf('8', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t12_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i]:
% 0.68/0.88         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.68/0.88      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (((k2_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B) = (sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf(t175_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ C ) =>
% 0.68/0.88       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.68/0.88         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.68/0.88         (((k10_relat_1 @ X42 @ (k2_xboole_0 @ X43 @ X44))
% 0.68/0.88            = (k2_xboole_0 @ (k10_relat_1 @ X42 @ X43) @ 
% 0.68/0.88               (k10_relat_1 @ X42 @ X44)))
% 0.68/0.88          | ~ (v1_relat_1 @ X42))),
% 0.68/0.88      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.68/0.88  thf(t11_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.88         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.68/0.88          | ~ (v1_relat_1 @ X2)
% 0.68/0.88          | (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ X3))),
% 0.68/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k10_relat_1 @ X1 @ sk_B) @ X0)
% 0.68/0.88          | (r1_tarski @ (k10_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.68/0.88             X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['10', '13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X0)
% 0.68/0.88          | (r1_tarski @ (k10_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.68/0.88             (k10_relat_1 @ X0 @ sk_B)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['7', '14'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.68/0.88         (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))
% 0.68/0.88        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['5', '15'])).
% 0.68/0.88  thf('17', plain, (![X53 : $i]: (v1_relat_1 @ (k6_relat_1 @ X53))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.68/0.88        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['16', '17'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X4 : $i, X6 : $i]:
% 0.68/0.88         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      ((~ (r1_tarski @ 
% 0.68/0.88           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B) @ 
% 0.68/0.88           (k10_relat_1 @ sk_A @ sk_C_1))
% 0.68/0.88        | ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.68/0.88            = (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.68/0.88  thf(d3_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('22', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.68/0.88      inference('simplify', [status(thm)], ['6'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.88         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.88          | (r2_hidden @ X0 @ X2)
% 0.68/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ X0 @ X1)
% 0.68/0.88          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['21', '26'])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.68/0.88         (((k10_relat_1 @ X42 @ (k2_xboole_0 @ X43 @ X44))
% 0.68/0.88            = (k2_xboole_0 @ (k10_relat_1 @ X42 @ X43) @ 
% 0.68/0.88               (k10_relat_1 @ X42 @ X44)))
% 0.68/0.88          | ~ (v1_relat_1 @ X42))),
% 0.68/0.88      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.68/0.88            = (k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 0.68/0.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.88  thf('31', plain, (![X53 : $i]: (v1_relat_1 @ (k6_relat_1 @ X53))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.68/0.88  thf(d13_funct_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88       ( ![B:$i,C:$i]:
% 0.68/0.88         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.68/0.88           ( ![D:$i]:
% 0.68/0.88             ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.88               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.68/0.88                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.68/0.88         (((X50) != (k10_relat_1 @ X49 @ X48))
% 0.68/0.88          | (r2_hidden @ X51 @ (k1_relat_1 @ X49))
% 0.68/0.88          | ~ (r2_hidden @ X51 @ X50)
% 0.68/0.88          | ~ (v1_funct_1 @ X49)
% 0.68/0.88          | ~ (v1_relat_1 @ X49))),
% 0.68/0.88      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X48 : $i, X49 : $i, X51 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X49)
% 0.68/0.88          | ~ (v1_funct_1 @ X49)
% 0.68/0.88          | ~ (r2_hidden @ X51 @ (k10_relat_1 @ X49 @ X48))
% 0.68/0.88          | (r2_hidden @ X51 @ (k1_relat_1 @ X49)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['33'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X2 @ 
% 0.68/0.88             (k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 0.68/0.88          | (r2_hidden @ X2 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.68/0.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.68/0.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['32', '34'])).
% 0.68/0.88  thf('36', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.68/0.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.88  thf('37', plain, (![X54 : $i]: (v1_funct_1 @ (k6_relat_1 @ X54))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('38', plain, (![X53 : $i]: (v1_relat_1 @ (k6_relat_1 @ X53))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X2 @ 
% 0.68/0.88             (k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 0.68/0.88          | (r2_hidden @ X2 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.68/0.88          | (r2_hidden @ 
% 0.68/0.88             (sk_C @ X2 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['27', '39'])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.68/0.88          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['40', '41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.68/0.88      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.68/0.88         = (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['20', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (![X41 : $i]:
% 0.68/0.88         (((k10_relat_1 @ X41 @ (k2_relat_1 @ X41)) = (k1_relat_1 @ X41))
% 0.68/0.88          | ~ (v1_relat_1 @ X41))),
% 0.68/0.88      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.68/0.88  thf('46', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.68/0.88      inference('simplify', [status(thm)], ['6'])).
% 0.68/0.88  thf(t147_funct_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.88       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.68/0.88         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      (![X58 : $i, X59 : $i]:
% 0.68/0.88         (~ (r1_tarski @ X58 @ (k2_relat_1 @ X59))
% 0.68/0.88          | ((k9_relat_1 @ X59 @ (k10_relat_1 @ X59 @ X58)) = (X58))
% 0.68/0.88          | ~ (v1_funct_1 @ X59)
% 0.68/0.88          | ~ (v1_relat_1 @ X59))),
% 0.68/0.88      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X0)
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.68/0.88              = (k2_relat_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['46', '47'])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.68/0.88          | ~ (v1_relat_1 @ X0)
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['45', '48'])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0)
% 0.68/0.88          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['49'])).
% 0.68/0.88  thf(t148_funct_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.88       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.68/0.88         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (![X60 : $i, X61 : $i]:
% 0.68/0.88         (((k9_relat_1 @ X61 @ (k10_relat_1 @ X61 @ X60))
% 0.68/0.88            = (k3_xboole_0 @ X60 @ (k9_relat_1 @ X61 @ (k1_relat_1 @ X61))))
% 0.68/0.88          | ~ (v1_funct_1 @ X61)
% 0.68/0.88          | ~ (v1_relat_1 @ X61))),
% 0.68/0.88      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.68/0.88            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.68/0.88          | ~ (v1_relat_1 @ X0)
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0)
% 0.68/0.88          | ~ (v1_funct_1 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['50', '51'])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0)
% 0.68/0.88          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.68/0.88              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['52'])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      ((((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.68/0.88          (k10_relat_1 @ sk_A @ sk_C_1))
% 0.68/0.88          = (k3_xboole_0 @ sk_B @ 
% 0.68/0.88             (k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))))
% 0.68/0.88        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.68/0.88        | ~ (v1_funct_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['44', '53'])).
% 0.68/0.88  thf('55', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.68/0.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      (![X60 : $i, X61 : $i]:
% 0.68/0.88         (((k9_relat_1 @ X61 @ (k10_relat_1 @ X61 @ X60))
% 0.68/0.88            = (k3_xboole_0 @ X60 @ (k9_relat_1 @ X61 @ (k1_relat_1 @ X61))))
% 0.68/0.88          | ~ (v1_funct_1 @ X61)
% 0.68/0.88          | ~ (v1_relat_1 @ X61))),
% 0.68/0.88      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.88            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.68/0.88            = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 0.68/0.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['55', '56'])).
% 0.68/0.88  thf('58', plain, (![X53 : $i]: (v1_relat_1 @ (k6_relat_1 @ X53))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('59', plain, (![X54 : $i]: (v1_funct_1 @ (k6_relat_1 @ X54))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.88           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.68/0.88           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.68/0.88  thf('61', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X0)
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.68/0.88              = (k2_relat_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['46', '47'])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.68/0.88            (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.68/0.88            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.68/0.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.68/0.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf('63', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.68/0.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.88           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.68/0.88           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.68/0.88           = (k3_xboole_0 @ X0 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['64', '65'])).
% 0.68/0.88  thf('67', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.68/0.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.88  thf('68', plain, (![X54 : $i]: (v1_funct_1 @ (k6_relat_1 @ X54))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('69', plain, (![X53 : $i]: (v1_relat_1 @ (k6_relat_1 @ X53))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['62', '63', '66', '67', '68', '69'])).
% 0.68/0.88  thf('71', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.68/0.88      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.88  thf('72', plain, (![X53 : $i]: (v1_relat_1 @ (k6_relat_1 @ X53))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('73', plain, (![X54 : $i]: (v1_funct_1 @ (k6_relat_1 @ X54))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.68/0.88         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['54', '70', '71', '72', '73'])).
% 0.68/0.88  thf(t139_funct_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ C ) =>
% 0.68/0.88       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.68/0.88         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.68/0.88         (((k10_relat_1 @ (k7_relat_1 @ X56 @ X55) @ X57)
% 0.68/0.88            = (k3_xboole_0 @ X55 @ (k10_relat_1 @ X56 @ X57)))
% 0.68/0.88          | ~ (v1_relat_1 @ X56))),
% 0.68/0.88      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.68/0.88  thf('76', plain,
% 0.68/0.88      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.68/0.88         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('77', plain,
% 0.68/0.88      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.68/0.88          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.68/0.88        | ~ (v1_relat_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['75', '76'])).
% 0.68/0.88  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.68/0.88         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['77', '78'])).
% 0.68/0.88  thf('80', plain, ($false),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['74', '79'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.74/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
