%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0385+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CeaATFUgus

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:49 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   89 (1601 expanded)
%              Number of leaves         :   17 ( 473 expanded)
%              Depth                    :   30
%              Number of atoms          :  785 (15235 expanded)
%              Number of equality atoms :   58 ( 699 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t3_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t3_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X18: $i] :
      ( ( X18
        = ( k3_tarski @ X14 ) )
      | ( r2_hidden @ ( sk_D_2 @ X18 @ X14 ) @ X14 )
      | ( r2_hidden @ ( sk_C_2 @ X18 @ X14 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X7: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X7 @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X3 ) @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('7',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X3 ) @ X3 )
      | ( r2_hidden @ X7 @ ( k1_setfam_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ ( sk_D_3 @ X17 @ X14 ) @ X14 )
      | ( X16
       != ( k3_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X14: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ X17 @ X14 ) @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k3_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C_1 @ X0 @ ( k3_tarski @ k1_xboole_0 ) ) @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C_1 @ X0 @ ( k3_tarski @ k1_xboole_0 ) ) @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( sk_D_3 @ ( sk_C_1 @ X1 @ ( k3_tarski @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) )
      | ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k3_tarski @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) )
      | ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k3_tarski @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X1 @ ( k3_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) )
      | ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) )
      | ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k1_setfam_1 @ ( k3_tarski @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k3_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['5','32'])).

thf('34',plain,(
    ! [X14: $i,X18: $i] :
      ( ( X18
        = ( k3_tarski @ X14 ) )
      | ( r2_hidden @ ( sk_C_2 @ X18 @ X14 ) @ ( sk_D_2 @ X18 @ X14 ) )
      | ( r2_hidden @ ( sk_C_2 @ X18 @ X14 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ~ ( r2_hidden @ X5 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X2 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('43',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X5 @ X3 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('48',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k3_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X15 @ ( k3_tarski @ X14 ) )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( k3_tarski @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_setfam_1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X3: $i,X8: $i] :
      ( ( X8
       != ( k1_setfam_1 @ X3 ) )
      | ( X8 = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('66',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('68',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('69',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64','66','67','68','69'])).


%------------------------------------------------------------------------------
