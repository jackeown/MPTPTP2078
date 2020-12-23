%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.70wHoXe7B7

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:42 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 198 expanded)
%              Number of leaves         :   30 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          : 1060 (1727 expanded)
%              Number of equality atoms :   43 (  99 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X41: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X53 @ ( k10_relat_1 @ X53 @ X54 ) ) @ X54 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X49: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( r1_tarski @ X62 @ ( k1_relat_1 @ X63 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X63 @ X62 ) @ X64 )
      | ( r1_tarski @ X62 @ ( k10_relat_1 @ X63 @ X64 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X49: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
      = ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
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

thf('30',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X45
       != ( k10_relat_1 @ X44 @ X43 ) )
      | ( r2_hidden @ X46 @ ( k1_relat_1 @ X44 ) )
      | ~ ( r2_hidden @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('31',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X46 @ ( k10_relat_1 @ X44 @ X43 ) )
      | ( r2_hidden @ X46 @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X49: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B )
    = ( k10_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X55 @ ( k1_relat_1 @ X56 ) )
      | ( r1_tarski @ X55 @ ( k10_relat_1 @ X56 @ ( k9_relat_1 @ X56 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t158_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( r1_tarski @ X59 @ X60 )
      | ~ ( v1_relat_1 @ X61 )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( r1_tarski @ X59 @ ( k2_relat_1 @ X61 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X61 @ X59 ) @ ( k10_relat_1 @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t158_funct_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('53',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X53 @ ( k10_relat_1 @ X53 @ X54 ) ) @ X54 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('60',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k9_relat_1 @ X58 @ ( k10_relat_1 @ X58 @ X57 ) )
        = ( k3_xboole_0 @ X57 @ ( k9_relat_1 @ X58 @ ( k1_relat_1 @ X58 ) ) ) )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['40','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('65',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('71',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( r1_tarski @ X59 @ X60 )
      | ~ ( v1_relat_1 @ X61 )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( r1_tarski @ X59 @ ( k2_relat_1 @ X61 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X61 @ X59 ) @ ( k10_relat_1 @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t158_funct_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X41: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('74',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('75',plain,(
    ! [X49: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('76',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['66','78'])).

thf('80',plain,(
    ! [X41: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('81',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('82',plain,(
    ! [X49: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('83',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['63','79','80','81','82'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('84',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X51 @ X50 ) @ X52 )
        = ( k3_xboole_0 @ X50 @ ( k10_relat_1 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('85',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.70wHoXe7B7
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.82  % Solved by: fo/fo7.sh
% 0.66/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.82  % done 477 iterations in 0.354s
% 0.66/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.82  % SZS output start Refutation
% 0.66/0.82  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.82  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.66/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.66/0.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.66/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.66/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.66/0.82  thf(t175_funct_2, conjecture,
% 0.66/0.82    (![A:$i]:
% 0.66/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.82       ( ![B:$i,C:$i]:
% 0.66/0.82         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.66/0.82           ( ( k10_relat_1 @ A @ C ) =
% 0.66/0.82             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.66/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.82    (~( ![A:$i]:
% 0.66/0.82        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.82          ( ![B:$i,C:$i]:
% 0.66/0.82            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.66/0.82              ( ( k10_relat_1 @ A @ C ) =
% 0.66/0.82                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.66/0.82    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.66/0.82  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.66/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.82  thf(t71_relat_1, axiom,
% 0.66/0.82    (![A:$i]:
% 0.66/0.82     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.66/0.82       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.66/0.82  thf('1', plain, (![X41 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.66/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.82  thf(t169_relat_1, axiom,
% 0.66/0.82    (![A:$i]:
% 0.66/0.82     ( ( v1_relat_1 @ A ) =>
% 0.66/0.82       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.66/0.82  thf('2', plain,
% 0.66/0.82      (![X39 : $i]:
% 0.66/0.82         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.66/0.82          | ~ (v1_relat_1 @ X39))),
% 0.66/0.82      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.66/0.82  thf('3', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.66/0.82            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.66/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.82      inference('sup+', [status(thm)], ['1', '2'])).
% 0.66/0.82  thf('4', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.66/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.82  thf(fc3_funct_1, axiom,
% 0.66/0.82    (![A:$i]:
% 0.66/0.82     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.66/0.82       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.66/0.82  thf('5', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('6', plain,
% 0.66/0.82      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.66/0.82      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.66/0.82  thf(t145_funct_1, axiom,
% 0.66/0.82    (![A:$i,B:$i]:
% 0.66/0.82     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.82       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.66/0.82  thf('7', plain,
% 0.66/0.82      (![X53 : $i, X54 : $i]:
% 0.66/0.82         ((r1_tarski @ (k9_relat_1 @ X53 @ (k10_relat_1 @ X53 @ X54)) @ X54)
% 0.66/0.82          | ~ (v1_funct_1 @ X53)
% 0.66/0.82          | ~ (v1_relat_1 @ X53))),
% 0.66/0.82      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.66/0.82  thf('8', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.66/0.82          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.82      inference('sup+', [status(thm)], ['6', '7'])).
% 0.66/0.82  thf('9', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('10', plain, (![X49 : $i]: (v1_funct_1 @ (k6_relat_1 @ X49))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('11', plain,
% 0.66/0.82      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.66/0.82      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.66/0.82  thf(t1_xboole_1, axiom,
% 0.66/0.82    (![A:$i,B:$i,C:$i]:
% 0.66/0.82     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.66/0.82       ( r1_tarski @ A @ C ) ))).
% 0.66/0.82  thf('12', plain,
% 0.66/0.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.82         (~ (r1_tarski @ X7 @ X8)
% 0.66/0.82          | ~ (r1_tarski @ X8 @ X9)
% 0.66/0.82          | (r1_tarski @ X7 @ X9))),
% 0.66/0.82      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.66/0.82  thf('13', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.66/0.82          | ~ (r1_tarski @ X0 @ X1))),
% 0.66/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.82  thf('14', plain,
% 0.66/0.82      ((r1_tarski @ 
% 0.66/0.82        (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.66/0.82         (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.66/0.82        sk_B)),
% 0.66/0.82      inference('sup-', [status(thm)], ['0', '13'])).
% 0.66/0.82  thf('15', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.66/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.82  thf(d10_xboole_0, axiom,
% 0.66/0.82    (![A:$i,B:$i]:
% 0.66/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.82  thf('16', plain,
% 0.66/0.82      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.66/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.82  thf('17', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.66/0.82      inference('simplify', [status(thm)], ['16'])).
% 0.66/0.82  thf(t163_funct_1, axiom,
% 0.66/0.82    (![A:$i,B:$i,C:$i]:
% 0.66/0.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.66/0.82       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.66/0.82           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.66/0.82         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.82  thf('18', plain,
% 0.66/0.82      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.66/0.82         (~ (r1_tarski @ X62 @ (k1_relat_1 @ X63))
% 0.66/0.82          | ~ (r1_tarski @ (k9_relat_1 @ X63 @ X62) @ X64)
% 0.66/0.82          | (r1_tarski @ X62 @ (k10_relat_1 @ X63 @ X64))
% 0.66/0.82          | ~ (v1_funct_1 @ X63)
% 0.66/0.82          | ~ (v1_relat_1 @ X63))),
% 0.66/0.82      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.66/0.82  thf('19', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.66/0.82          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.66/0.82      inference('sup-', [status(thm)], ['17', '18'])).
% 0.66/0.82  thf('20', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.66/0.82          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.66/0.82             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.66/0.82          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.66/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.82      inference('sup-', [status(thm)], ['15', '19'])).
% 0.66/0.82  thf('21', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.66/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.82  thf('22', plain, (![X49 : $i]: (v1_funct_1 @ (k6_relat_1 @ X49))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('23', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('24', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.66/0.82          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.66/0.82      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.66/0.82  thf('25', plain,
% 0.66/0.82      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.66/0.82        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))),
% 0.66/0.82      inference('sup-', [status(thm)], ['14', '24'])).
% 0.66/0.82  thf('26', plain,
% 0.66/0.82      (![X4 : $i, X6 : $i]:
% 0.66/0.82         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.82  thf('27', plain,
% 0.66/0.82      ((~ (r1_tarski @ 
% 0.66/0.82           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B) @ 
% 0.66/0.82           (k10_relat_1 @ sk_A @ sk_C_1))
% 0.66/0.82        | ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.66/0.82            = (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.66/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.66/0.82  thf('28', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.66/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.82  thf(d3_tarski, axiom,
% 0.66/0.82    (![A:$i,B:$i]:
% 0.66/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.82  thf('29', plain,
% 0.66/0.82      (![X1 : $i, X3 : $i]:
% 0.66/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.66/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.82  thf(d13_funct_1, axiom,
% 0.66/0.82    (![A:$i]:
% 0.66/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.82       ( ![B:$i,C:$i]:
% 0.66/0.82         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.66/0.82           ( ![D:$i]:
% 0.66/0.82             ( ( r2_hidden @ D @ C ) <=>
% 0.66/0.82               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.66/0.82                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.66/0.82  thf('30', plain,
% 0.66/0.82      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.66/0.82         (((X45) != (k10_relat_1 @ X44 @ X43))
% 0.66/0.82          | (r2_hidden @ X46 @ (k1_relat_1 @ X44))
% 0.66/0.82          | ~ (r2_hidden @ X46 @ X45)
% 0.66/0.82          | ~ (v1_funct_1 @ X44)
% 0.66/0.82          | ~ (v1_relat_1 @ X44))),
% 0.66/0.82      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.66/0.82  thf('31', plain,
% 0.66/0.82      (![X43 : $i, X44 : $i, X46 : $i]:
% 0.66/0.82         (~ (v1_relat_1 @ X44)
% 0.66/0.82          | ~ (v1_funct_1 @ X44)
% 0.66/0.82          | ~ (r2_hidden @ X46 @ (k10_relat_1 @ X44 @ X43))
% 0.66/0.82          | (r2_hidden @ X46 @ (k1_relat_1 @ X44)))),
% 0.66/0.82      inference('simplify', [status(thm)], ['30'])).
% 0.66/0.82  thf('32', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.82         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.66/0.82          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.66/0.82             (k1_relat_1 @ X1))
% 0.66/0.82          | ~ (v1_funct_1 @ X1)
% 0.66/0.82          | ~ (v1_relat_1 @ X1))),
% 0.66/0.82      inference('sup-', [status(thm)], ['29', '31'])).
% 0.66/0.82  thf('33', plain,
% 0.66/0.82      (![X1 : $i, X3 : $i]:
% 0.66/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.66/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.82  thf('34', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.66/0.82          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.66/0.82      inference('sup-', [status(thm)], ['32', '33'])).
% 0.66/0.82  thf('35', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0))),
% 0.66/0.82      inference('simplify', [status(thm)], ['34'])).
% 0.66/0.82  thf('36', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.66/0.82          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.82      inference('sup+', [status(thm)], ['28', '35'])).
% 0.66/0.82  thf('37', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('38', plain, (![X49 : $i]: (v1_funct_1 @ (k6_relat_1 @ X49))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('39', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.66/0.82      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.66/0.82  thf('40', plain,
% 0.66/0.82      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)
% 0.66/0.82         = (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.66/0.82      inference('demod', [status(thm)], ['27', '39'])).
% 0.66/0.82  thf('41', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.66/0.82      inference('simplify', [status(thm)], ['16'])).
% 0.66/0.82  thf(t146_funct_1, axiom,
% 0.66/0.82    (![A:$i,B:$i]:
% 0.66/0.82     ( ( v1_relat_1 @ B ) =>
% 0.66/0.82       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.66/0.82         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.66/0.82  thf('42', plain,
% 0.66/0.82      (![X55 : $i, X56 : $i]:
% 0.66/0.82         (~ (r1_tarski @ X55 @ (k1_relat_1 @ X56))
% 0.66/0.82          | (r1_tarski @ X55 @ (k10_relat_1 @ X56 @ (k9_relat_1 @ X56 @ X55)))
% 0.66/0.82          | ~ (v1_relat_1 @ X56))),
% 0.66/0.82      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.66/0.82  thf('43', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (~ (v1_relat_1 @ X0)
% 0.66/0.82          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.66/0.82             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.66/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.66/0.82  thf('44', plain,
% 0.66/0.82      (![X39 : $i]:
% 0.66/0.82         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.66/0.82          | ~ (v1_relat_1 @ X39))),
% 0.66/0.82      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.66/0.82  thf(t158_funct_1, axiom,
% 0.66/0.82    (![A:$i,B:$i,C:$i]:
% 0.66/0.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.66/0.82       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.66/0.82           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.66/0.82         ( r1_tarski @ A @ B ) ) ))).
% 0.66/0.82  thf('45', plain,
% 0.66/0.82      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.66/0.82         ((r1_tarski @ X59 @ X60)
% 0.66/0.82          | ~ (v1_relat_1 @ X61)
% 0.66/0.82          | ~ (v1_funct_1 @ X61)
% 0.66/0.82          | ~ (r1_tarski @ X59 @ (k2_relat_1 @ X61))
% 0.66/0.82          | ~ (r1_tarski @ (k10_relat_1 @ X61 @ X59) @ 
% 0.66/0.82               (k10_relat_1 @ X61 @ X60)))),
% 0.66/0.82      inference('cnf', [status(esa)], [t158_funct_1])).
% 0.66/0.82  thf('46', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.66/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.66/0.82  thf('47', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.66/0.82      inference('simplify', [status(thm)], ['16'])).
% 0.66/0.82  thf('48', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.66/0.82      inference('demod', [status(thm)], ['46', '47'])).
% 0.66/0.82  thf('49', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))),
% 0.66/0.82      inference('simplify', [status(thm)], ['48'])).
% 0.66/0.82  thf('50', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.66/0.82             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.66/0.82      inference('sup-', [status(thm)], ['43', '49'])).
% 0.66/0.82  thf('51', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.66/0.82           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0))),
% 0.66/0.82      inference('simplify', [status(thm)], ['50'])).
% 0.66/0.82  thf('52', plain,
% 0.66/0.82      (![X39 : $i]:
% 0.66/0.82         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.66/0.82          | ~ (v1_relat_1 @ X39))),
% 0.66/0.82      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.66/0.82  thf('53', plain,
% 0.66/0.82      (![X53 : $i, X54 : $i]:
% 0.66/0.82         ((r1_tarski @ (k9_relat_1 @ X53 @ (k10_relat_1 @ X53 @ X54)) @ X54)
% 0.66/0.82          | ~ (v1_funct_1 @ X53)
% 0.66/0.82          | ~ (v1_relat_1 @ X53))),
% 0.66/0.82      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.66/0.82  thf('54', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         ((r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.66/0.82           (k2_relat_1 @ X0))
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0))),
% 0.66/0.82      inference('sup+', [status(thm)], ['52', '53'])).
% 0.66/0.82  thf('55', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.66/0.82             (k2_relat_1 @ X0)))),
% 0.66/0.82      inference('simplify', [status(thm)], ['54'])).
% 0.66/0.82  thf('56', plain,
% 0.66/0.82      (![X4 : $i, X6 : $i]:
% 0.66/0.82         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.82  thf('57', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.66/0.82               (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.66/0.82          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.66/0.82      inference('sup-', [status(thm)], ['55', '56'])).
% 0.66/0.82  thf('58', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0))),
% 0.66/0.82      inference('sup-', [status(thm)], ['51', '57'])).
% 0.66/0.82  thf('59', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0))),
% 0.66/0.82      inference('simplify', [status(thm)], ['58'])).
% 0.66/0.82  thf(t148_funct_1, axiom,
% 0.66/0.82    (![A:$i,B:$i]:
% 0.66/0.82     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.82       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.66/0.82         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.66/0.82  thf('60', plain,
% 0.66/0.82      (![X57 : $i, X58 : $i]:
% 0.66/0.82         (((k9_relat_1 @ X58 @ (k10_relat_1 @ X58 @ X57))
% 0.66/0.82            = (k3_xboole_0 @ X57 @ (k9_relat_1 @ X58 @ (k1_relat_1 @ X58))))
% 0.66/0.82          | ~ (v1_funct_1 @ X58)
% 0.66/0.82          | ~ (v1_relat_1 @ X58))),
% 0.66/0.82      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.66/0.82  thf('61', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.66/0.82            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ~ (v1_funct_1 @ X0))),
% 0.66/0.82      inference('sup+', [status(thm)], ['59', '60'])).
% 0.66/0.82  thf('62', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (v1_funct_1 @ X0)
% 0.66/0.82          | ~ (v1_relat_1 @ X0)
% 0.66/0.82          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.66/0.82              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.66/0.82      inference('simplify', [status(thm)], ['61'])).
% 0.66/0.82  thf('63', plain,
% 0.66/0.82      ((((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.66/0.82          (k10_relat_1 @ sk_A @ sk_C_1))
% 0.66/0.82          = (k3_xboole_0 @ sk_B @ 
% 0.66/0.82             (k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))))
% 0.66/0.82        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.66/0.82        | ~ (v1_funct_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1))))),
% 0.66/0.82      inference('sup+', [status(thm)], ['40', '62'])).
% 0.66/0.82  thf('64', plain,
% 0.66/0.82      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.66/0.82      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.66/0.82  thf('65', plain,
% 0.66/0.82      (![X4 : $i, X6 : $i]:
% 0.66/0.82         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.82  thf('66', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (~ (r1_tarski @ X0 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.66/0.82          | ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.66/0.82      inference('sup-', [status(thm)], ['64', '65'])).
% 0.66/0.82  thf('67', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.66/0.82      inference('simplify', [status(thm)], ['16'])).
% 0.66/0.82  thf('68', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.66/0.82          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.66/0.82      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.66/0.82  thf('69', plain,
% 0.66/0.82      (![X0 : $i]:
% 0.66/0.82         (r1_tarski @ X0 @ 
% 0.66/0.82          (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.66/0.82           (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.66/0.82      inference('sup-', [status(thm)], ['67', '68'])).
% 0.66/0.82  thf('70', plain,
% 0.66/0.82      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.66/0.82      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.66/0.82  thf('71', plain,
% 0.66/0.82      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.66/0.82         ((r1_tarski @ X59 @ X60)
% 0.66/0.82          | ~ (v1_relat_1 @ X61)
% 0.66/0.82          | ~ (v1_funct_1 @ X61)
% 0.66/0.82          | ~ (r1_tarski @ X59 @ (k2_relat_1 @ X61))
% 0.66/0.82          | ~ (r1_tarski @ (k10_relat_1 @ X61 @ X59) @ 
% 0.66/0.82               (k10_relat_1 @ X61 @ X60)))),
% 0.66/0.82      inference('cnf', [status(esa)], [t158_funct_1])).
% 0.66/0.82  thf('72', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.66/0.82          | ~ (r1_tarski @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.66/0.82          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.66/0.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.66/0.82          | (r1_tarski @ X0 @ X1))),
% 0.66/0.82      inference('sup-', [status(thm)], ['70', '71'])).
% 0.66/0.82  thf('73', plain, (![X41 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.66/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.82  thf('74', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.66/0.82      inference('simplify', [status(thm)], ['16'])).
% 0.66/0.82  thf('75', plain, (![X49 : $i]: (v1_funct_1 @ (k6_relat_1 @ X49))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('76', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('77', plain,
% 0.66/0.82      (![X0 : $i, X1 : $i]:
% 0.66/0.82         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.66/0.82          | (r1_tarski @ X0 @ X1))),
% 0.66/0.82      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.66/0.82  thf('78', plain,
% 0.66/0.82      (![X0 : $i]: (r1_tarski @ X0 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.66/0.82      inference('sup-', [status(thm)], ['69', '77'])).
% 0.66/0.82  thf('79', plain,
% 0.66/0.82      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.66/0.82      inference('demod', [status(thm)], ['66', '78'])).
% 0.66/0.82  thf('80', plain, (![X41 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.66/0.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.82  thf('81', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('82', plain, (![X49 : $i]: (v1_funct_1 @ (k6_relat_1 @ X49))),
% 0.66/0.82      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.82  thf('83', plain,
% 0.66/0.82      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.66/0.82         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.66/0.82      inference('demod', [status(thm)], ['63', '79', '80', '81', '82'])).
% 0.66/0.82  thf(t139_funct_1, axiom,
% 0.66/0.82    (![A:$i,B:$i,C:$i]:
% 0.66/0.82     ( ( v1_relat_1 @ C ) =>
% 0.66/0.82       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.66/0.82         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.82  thf('84', plain,
% 0.66/0.82      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.66/0.82         (((k10_relat_1 @ (k7_relat_1 @ X51 @ X50) @ X52)
% 0.66/0.82            = (k3_xboole_0 @ X50 @ (k10_relat_1 @ X51 @ X52)))
% 0.66/0.82          | ~ (v1_relat_1 @ X51))),
% 0.66/0.82      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.66/0.82  thf('85', plain,
% 0.66/0.82      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.66/0.82         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.66/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.82  thf('86', plain,
% 0.66/0.82      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.66/0.82          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.66/0.82        | ~ (v1_relat_1 @ sk_A))),
% 0.66/0.82      inference('sup-', [status(thm)], ['84', '85'])).
% 0.66/0.82  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.66/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.82  thf('88', plain,
% 0.66/0.82      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.66/0.82         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.66/0.82      inference('demod', [status(thm)], ['86', '87'])).
% 0.66/0.82  thf('89', plain, ($false),
% 0.66/0.82      inference('simplify_reflect-', [status(thm)], ['83', '88'])).
% 0.66/0.82  
% 0.66/0.82  % SZS output end Refutation
% 0.66/0.82  
% 0.66/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
