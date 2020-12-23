%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fp0MaV7rng

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 205 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   20
%              Number of atoms          :  944 (2581 expanded)
%              Number of equality atoms :   66 ( 182 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ( X12
       != ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_funct_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t72_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ B )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_funct_1])).

thf('18',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X16 )
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ( ( k1_funct_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ( ( k1_funct_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['35','48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('56',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
        = ( k1_funct_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['35','48'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fp0MaV7rng
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 179 iterations in 0.090s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(d4_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.21/0.55         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.21/0.55          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.21/0.55          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X6 @ X5)
% 0.21/0.55          | (r2_hidden @ X6 @ X4)
% 0.21/0.55          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.55         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X1 @ X0)
% 0.21/0.55            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.21/0.55             X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.21/0.55         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.21/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X1 @ X0)
% 0.21/0.55            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.55          | ((k3_xboole_0 @ X1 @ X0)
% 0.21/0.55              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X1 @ X0)
% 0.21/0.55           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.55  thf(fc8_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.21/0.55         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (v1_funct_1 @ X14)
% 0.21/0.55          | ~ (v1_relat_1 @ X14)
% 0.21/0.55          | (v1_funct_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (v1_funct_1 @ X14)
% 0.21/0.55          | ~ (v1_relat_1 @ X14)
% 0.21/0.55          | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.55  thf(t90_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.55         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k7_relat_1 @ X8 @ X9))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.21/0.55          | ~ (v1_relat_1 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.55  thf(d4_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ![B:$i,C:$i]:
% 0.21/0.55         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.55               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.55           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.55               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         ((r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.21/0.55          | ((X12) = (k1_xboole_0))
% 0.21/0.55          | ((X12) != (k1_funct_1 @ X11 @ X10))
% 0.21/0.55          | ~ (v1_funct_1 @ X11)
% 0.21/0.55          | ~ (v1_relat_1 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X11)
% 0.21/0.55          | ~ (v1_funct_1 @ X11)
% 0.21/0.55          | ((k1_funct_1 @ X11 @ X10) = (k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.55  thf(t72_funct_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55       ( ( r2_hidden @ A @ B ) =>
% 0.21/0.55         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55          ( ( r2_hidden @ A @ B ) =>
% 0.21/0.55            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.21/0.55              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t72_funct_1])).
% 0.21/0.55  thf('18', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.55          | ~ (r2_hidden @ X2 @ X4)
% 0.21/0.55          | (r2_hidden @ X2 @ X5)
% 0.21/0.55          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.55         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.21/0.55          | ~ (r2_hidden @ X2 @ X4)
% 0.21/0.55          | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ sk_A @ X0)
% 0.21/0.55          | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_funct_1 @ X0 @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ sk_A @ 
% 0.21/0.55           (k3_xboole_0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ sk_B))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['15', '22'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ sk_A @ 
% 0.21/0.55           (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | (r2_hidden @ sk_A @ 
% 0.21/0.55             (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ sk_A @ 
% 0.21/0.55           (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.21/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ sk_A @ 
% 0.21/0.55             (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ sk_A @ 
% 0.21/0.55           (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ sk_B))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['12', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.55         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ sk_A @ (k1_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.55         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_funct_1 @ X0 @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k7_relat_1 @ X8 @ X9))
% 0.21/0.55            = (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.21/0.55          | ~ (v1_relat_1 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.55  thf(t70_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.21/0.55         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X16 @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X18)))
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X17 @ X18) @ X16)
% 0.21/0.55              = (k1_funct_1 @ X17 @ X16))
% 0.21/0.55          | ~ (v1_funct_1 @ X17)
% 0.21/0.55          | ~ (v1_relat_1 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.55              = (k1_funct_1 @ X1 @ X2)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_funct_1 @ X1 @ X2))
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ X0 @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.21/0.55              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['36', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.21/0.55            = (k1_funct_1 @ X0 @ sk_A))
% 0.21/0.55          | ((k1_funct_1 @ X0 @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.55         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.21/0.55        | ((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.55  thf('48', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) != (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['35', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['34', '49'])).
% 0.21/0.55  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.55  thf('54', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.21/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ sk_A @ X0)
% 0.21/0.55          | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_funct_1 @ X1 @ X2))
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.21/0.55              = (k1_funct_1 @ X0 @ X2)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      ((((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.55          = (k1_funct_1 @ sk_C @ sk_A))
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['58', '61'])).
% 0.21/0.55  thf('63', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.55  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) != (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['35', '48'])).
% 0.21/0.55  thf('68', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
