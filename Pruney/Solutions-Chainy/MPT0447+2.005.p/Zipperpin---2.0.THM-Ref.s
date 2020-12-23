%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.neBQ2daQDn

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:53 EST 2020

% Result     : Theorem 3.42s
% Output     : Refutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 849 expanded)
%              Number of leaves         :   45 ( 297 expanded)
%              Depth                    :   24
%              Number of atoms          : 1210 (6163 expanded)
%              Number of equality atoms :   77 ( 352 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X52 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X52 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('13',plain,(
    ! [X45: $i,X48: $i] :
      ( ( X48
        = ( k1_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X48 @ X45 ) @ ( sk_D_1 @ X48 @ X45 ) ) @ X45 )
      | ( r2_hidden @ ( sk_C_1 @ X48 @ X45 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('14',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('28',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('29',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','25','26','27','28','29','30'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( r1_tarski @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('45',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('49',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k3_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k3_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['47','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('63',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('65',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('67',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X56 ) @ ( k2_relat_1 @ X55 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X56 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('68',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('70',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X56 ) @ ( k2_relat_1 @ X55 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X56 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('74',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('75',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('76',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('77',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('79',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('80',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( r1_tarski @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('84',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','87'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('92',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('93',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('94',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X53 ) @ ( k1_relat_1 @ X53 ) )
      | ~ ( r2_hidden @ X54 @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('97',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('102',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('103',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('114',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('117',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','115','116'])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','117'])).

thf('119',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('120',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','120'])).

thf('122',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('123',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('124',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','120'])).

thf('125',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['73','121','122','123','124','125','126'])).

thf('128',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('129',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['65','132'])).

thf('134',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('135',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( r1_tarski @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['0','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.neBQ2daQDn
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.42/3.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.42/3.64  % Solved by: fo/fo7.sh
% 3.42/3.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.42/3.64  % done 4598 iterations in 3.188s
% 3.42/3.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.42/3.64  % SZS output start Refutation
% 3.42/3.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.42/3.64  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 3.42/3.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.42/3.64  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.42/3.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.42/3.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.42/3.64  thf(sk_A_type, type, sk_A: $i).
% 3.42/3.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.42/3.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.42/3.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.42/3.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.42/3.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.42/3.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.42/3.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.42/3.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.42/3.64  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 3.42/3.64  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.42/3.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.42/3.64  thf(sk_B_type, type, sk_B: $i > $i).
% 3.42/3.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.42/3.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.42/3.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.42/3.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.42/3.64  thf(t31_relat_1, conjecture,
% 3.42/3.64    (![A:$i]:
% 3.42/3.64     ( ( v1_relat_1 @ A ) =>
% 3.42/3.64       ( ![B:$i]:
% 3.42/3.64         ( ( v1_relat_1 @ B ) =>
% 3.42/3.64           ( ( r1_tarski @ A @ B ) =>
% 3.42/3.64             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 3.42/3.64  thf(zf_stmt_0, negated_conjecture,
% 3.42/3.64    (~( ![A:$i]:
% 3.42/3.64        ( ( v1_relat_1 @ A ) =>
% 3.42/3.64          ( ![B:$i]:
% 3.42/3.64            ( ( v1_relat_1 @ B ) =>
% 3.42/3.64              ( ( r1_tarski @ A @ B ) =>
% 3.42/3.64                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 3.42/3.64    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 3.42/3.64  thf('0', plain,
% 3.42/3.64      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 3.42/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.64  thf(d6_relat_1, axiom,
% 3.42/3.64    (![A:$i]:
% 3.42/3.64     ( ( v1_relat_1 @ A ) =>
% 3.42/3.64       ( ( k3_relat_1 @ A ) =
% 3.42/3.64         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 3.42/3.64  thf('1', plain,
% 3.42/3.64      (![X50 : $i]:
% 3.42/3.64         (((k3_relat_1 @ X50)
% 3.42/3.64            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 3.42/3.64          | ~ (v1_relat_1 @ X50))),
% 3.42/3.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 3.42/3.64  thf('2', plain,
% 3.42/3.64      (![X50 : $i]:
% 3.42/3.64         (((k3_relat_1 @ X50)
% 3.42/3.64            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 3.42/3.64          | ~ (v1_relat_1 @ X50))),
% 3.42/3.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 3.42/3.64  thf('3', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 3.42/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.64  thf(l32_xboole_1, axiom,
% 3.42/3.64    (![A:$i,B:$i]:
% 3.42/3.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.42/3.64  thf('4', plain,
% 3.42/3.64      (![X9 : $i, X11 : $i]:
% 3.42/3.64         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 3.42/3.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.42/3.64  thf('5', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 3.42/3.64      inference('sup-', [status(thm)], ['3', '4'])).
% 3.42/3.64  thf(t15_relat_1, axiom,
% 3.42/3.64    (![A:$i]:
% 3.42/3.64     ( ( v1_relat_1 @ A ) =>
% 3.42/3.64       ( ![B:$i]:
% 3.42/3.64         ( ( v1_relat_1 @ B ) =>
% 3.42/3.64           ( r1_tarski @
% 3.42/3.64             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 3.42/3.64             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.42/3.64  thf('6', plain,
% 3.42/3.64      (![X51 : $i, X52 : $i]:
% 3.42/3.64         (~ (v1_relat_1 @ X51)
% 3.42/3.64          | (r1_tarski @ 
% 3.42/3.64             (k6_subset_1 @ (k1_relat_1 @ X52) @ (k1_relat_1 @ X51)) @ 
% 3.42/3.64             (k1_relat_1 @ (k6_subset_1 @ X52 @ X51)))
% 3.42/3.64          | ~ (v1_relat_1 @ X52))),
% 3.42/3.64      inference('cnf', [status(esa)], [t15_relat_1])).
% 3.42/3.64  thf(redefinition_k6_subset_1, axiom,
% 3.42/3.64    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.42/3.64  thf('7', plain,
% 3.42/3.64      (![X38 : $i, X39 : $i]:
% 3.42/3.64         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 3.42/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.42/3.64  thf('8', plain,
% 3.42/3.64      (![X38 : $i, X39 : $i]:
% 3.42/3.64         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 3.42/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.42/3.64  thf('9', plain,
% 3.42/3.64      (![X51 : $i, X52 : $i]:
% 3.42/3.64         (~ (v1_relat_1 @ X51)
% 3.42/3.64          | (r1_tarski @ 
% 3.42/3.64             (k4_xboole_0 @ (k1_relat_1 @ X52) @ (k1_relat_1 @ X51)) @ 
% 3.42/3.64             (k1_relat_1 @ (k4_xboole_0 @ X52 @ X51)))
% 3.42/3.64          | ~ (v1_relat_1 @ X52))),
% 3.42/3.64      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.42/3.64  thf(d10_xboole_0, axiom,
% 3.42/3.64    (![A:$i,B:$i]:
% 3.42/3.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.42/3.64  thf('10', plain,
% 3.42/3.64      (![X6 : $i, X8 : $i]:
% 3.42/3.64         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 3.42/3.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.42/3.64  thf('11', plain,
% 3.42/3.64      (![X0 : $i, X1 : $i]:
% 3.42/3.64         (~ (v1_relat_1 @ X1)
% 3.42/3.64          | ~ (v1_relat_1 @ X0)
% 3.42/3.64          | ~ (r1_tarski @ (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 3.42/3.64               (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 3.42/3.64          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 3.42/3.64              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 3.42/3.64      inference('sup-', [status(thm)], ['9', '10'])).
% 3.42/3.64  thf('12', plain,
% 3.42/3.64      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ 
% 3.42/3.64           (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 3.42/3.64        | ((k1_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 3.42/3.64            = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 3.42/3.64        | ~ (v1_relat_1 @ sk_B_1)
% 3.42/3.64        | ~ (v1_relat_1 @ sk_A))),
% 3.42/3.64      inference('sup-', [status(thm)], ['5', '11'])).
% 3.42/3.64  thf(d4_relat_1, axiom,
% 3.42/3.64    (![A:$i,B:$i]:
% 3.42/3.64     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.42/3.64       ( ![C:$i]:
% 3.42/3.64         ( ( r2_hidden @ C @ B ) <=>
% 3.42/3.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.42/3.64  thf('13', plain,
% 3.42/3.64      (![X45 : $i, X48 : $i]:
% 3.42/3.64         (((X48) = (k1_relat_1 @ X45))
% 3.42/3.64          | (r2_hidden @ 
% 3.42/3.64             (k4_tarski @ (sk_C_1 @ X48 @ X45) @ (sk_D_1 @ X48 @ X45)) @ X45)
% 3.42/3.64          | (r2_hidden @ (sk_C_1 @ X48 @ X45) @ X48))),
% 3.42/3.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.42/3.64  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 3.42/3.64  thf('14', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 3.42/3.64      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.42/3.64  thf(t7_xboole_0, axiom,
% 3.42/3.64    (![A:$i]:
% 3.42/3.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.42/3.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 3.42/3.64  thf('15', plain,
% 3.42/3.64      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 3.42/3.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.42/3.64  thf(t4_xboole_0, axiom,
% 3.42/3.64    (![A:$i,B:$i]:
% 3.42/3.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 3.42/3.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.42/3.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.42/3.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 3.42/3.64  thf('16', plain,
% 3.42/3.64      (![X1 : $i, X3 : $i, X4 : $i]:
% 3.42/3.64         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 3.42/3.64          | ~ (r1_xboole_0 @ X1 @ X4))),
% 3.42/3.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.42/3.64  thf('17', plain,
% 3.42/3.64      (![X0 : $i, X1 : $i]:
% 3.42/3.64         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['15', '16'])).
% 3.42/3.65  thf('18', plain,
% 3.42/3.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['14', '17'])).
% 3.42/3.65  thf('19', plain,
% 3.42/3.65      (![X1 : $i, X3 : $i, X4 : $i]:
% 3.42/3.65         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 3.42/3.65          | ~ (r1_xboole_0 @ X1 @ X4))),
% 3.42/3.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.42/3.65  thf('20', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['18', '19'])).
% 3.42/3.65  thf('21', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 3.42/3.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.42/3.65  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 3.42/3.65      inference('demod', [status(thm)], ['20', '21'])).
% 3.42/3.65  thf('23', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 3.42/3.65          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['13', '22'])).
% 3.42/3.65  thf('24', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 3.42/3.65      inference('demod', [status(thm)], ['20', '21'])).
% 3.42/3.65  thf('25', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['23', '24'])).
% 3.42/3.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.42/3.65  thf('26', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 3.42/3.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.42/3.65  thf('27', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['3', '4'])).
% 3.42/3.65  thf('28', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['23', '24'])).
% 3.42/3.65  thf('29', plain, ((v1_relat_1 @ sk_B_1)),
% 3.42/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.65  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 3.42/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.65  thf('31', plain,
% 3.42/3.65      (((k1_xboole_0)
% 3.42/3.65         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 3.42/3.65      inference('demod', [status(thm)],
% 3.42/3.65                ['12', '25', '26', '27', '28', '29', '30'])).
% 3.42/3.65  thf(t44_xboole_1, axiom,
% 3.42/3.65    (![A:$i,B:$i,C:$i]:
% 3.42/3.65     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.42/3.65       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.42/3.65  thf('32', plain,
% 3.42/3.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.42/3.65         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 3.42/3.65          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 3.42/3.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.42/3.65  thf('33', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.42/3.65          | (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 3.42/3.65             (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ X0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['31', '32'])).
% 3.42/3.65  thf('34', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 3.42/3.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.42/3.65  thf('35', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 3.42/3.65          (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ X0))),
% 3.42/3.65      inference('demod', [status(thm)], ['33', '34'])).
% 3.42/3.65  thf('36', plain,
% 3.42/3.65      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 3.42/3.65        | ~ (v1_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup+', [status(thm)], ['2', '35'])).
% 3.42/3.65  thf('37', plain, ((v1_relat_1 @ sk_B_1)),
% 3.42/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.65  thf('38', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('demod', [status(thm)], ['36', '37'])).
% 3.42/3.65  thf('39', plain,
% 3.42/3.65      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 3.42/3.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.42/3.65  thf('40', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 3.42/3.65      inference('simplify', [status(thm)], ['39'])).
% 3.42/3.65  thf(t8_xboole_1, axiom,
% 3.42/3.65    (![A:$i,B:$i,C:$i]:
% 3.42/3.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 3.42/3.65       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.42/3.65  thf('41', plain,
% 3.42/3.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.42/3.65         (~ (r1_tarski @ X29 @ X30)
% 3.42/3.65          | ~ (r1_tarski @ X31 @ X30)
% 3.42/3.65          | (r1_tarski @ (k2_xboole_0 @ X29 @ X31) @ X30))),
% 3.42/3.65      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.42/3.65  thf('42', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['40', '41'])).
% 3.42/3.65  thf('43', plain,
% 3.42/3.65      ((r1_tarski @ 
% 3.42/3.65        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 3.42/3.65        (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup-', [status(thm)], ['38', '42'])).
% 3.42/3.65  thf(t7_xboole_1, axiom,
% 3.42/3.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.42/3.65  thf('44', plain,
% 3.42/3.65      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 3.42/3.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.42/3.65  thf('45', plain,
% 3.42/3.65      (![X6 : $i, X8 : $i]:
% 3.42/3.65         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 3.42/3.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.42/3.65  thf('46', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 3.42/3.65          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['44', '45'])).
% 3.42/3.65  thf('47', plain,
% 3.42/3.65      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 3.42/3.65         = (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup-', [status(thm)], ['43', '46'])).
% 3.42/3.65  thf('48', plain,
% 3.42/3.65      (![X50 : $i]:
% 3.42/3.65         (((k3_relat_1 @ X50)
% 3.42/3.65            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 3.42/3.65          | ~ (v1_relat_1 @ X50))),
% 3.42/3.65      inference('cnf', [status(esa)], [d6_relat_1])).
% 3.42/3.65  thf('49', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 3.42/3.65      inference('simplify', [status(thm)], ['39'])).
% 3.42/3.65  thf(t10_xboole_1, axiom,
% 3.42/3.65    (![A:$i,B:$i,C:$i]:
% 3.42/3.65     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.42/3.65  thf('50', plain,
% 3.42/3.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.42/3.65         (~ (r1_tarski @ X12 @ X13)
% 3.42/3.65          | (r1_tarski @ X12 @ (k2_xboole_0 @ X14 @ X13)))),
% 3.42/3.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.42/3.65  thf('51', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['49', '50'])).
% 3.42/3.65  thf('52', plain,
% 3.42/3.65      (![X9 : $i, X11 : $i]:
% 3.42/3.65         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 3.42/3.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.42/3.65  thf('53', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['51', '52'])).
% 3.42/3.65  thf('54', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         (((k4_xboole_0 @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 3.42/3.65            = (k1_xboole_0))
% 3.42/3.65          | ~ (v1_relat_1 @ X0))),
% 3.42/3.65      inference('sup+', [status(thm)], ['48', '53'])).
% 3.42/3.65  thf('55', plain,
% 3.42/3.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.42/3.65         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 3.42/3.65          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 3.42/3.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.42/3.65  thf('56', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.42/3.65          | ~ (v1_relat_1 @ X1)
% 3.42/3.65          | (r1_tarski @ (k2_relat_1 @ X1) @ 
% 3.42/3.65             (k2_xboole_0 @ (k3_relat_1 @ X1) @ X0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['54', '55'])).
% 3.42/3.65  thf('57', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 3.42/3.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.42/3.65  thf('58', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (v1_relat_1 @ X1)
% 3.42/3.65          | (r1_tarski @ (k2_relat_1 @ X1) @ 
% 3.42/3.65             (k2_xboole_0 @ (k3_relat_1 @ X1) @ X0)))),
% 3.42/3.65      inference('demod', [status(thm)], ['56', '57'])).
% 3.42/3.65  thf('59', plain,
% 3.42/3.65      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 3.42/3.65        | ~ (v1_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup+', [status(thm)], ['47', '58'])).
% 3.42/3.65  thf('60', plain, ((v1_relat_1 @ sk_B_1)),
% 3.42/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.65  thf('61', plain,
% 3.42/3.65      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('demod', [status(thm)], ['59', '60'])).
% 3.42/3.65  thf('62', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['40', '41'])).
% 3.42/3.65  thf('63', plain,
% 3.42/3.65      ((r1_tarski @ 
% 3.42/3.65        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1)) @ 
% 3.42/3.65        (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup-', [status(thm)], ['61', '62'])).
% 3.42/3.65  thf('64', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 3.42/3.65          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['44', '45'])).
% 3.42/3.65  thf('65', plain,
% 3.42/3.65      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))
% 3.42/3.65         = (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup-', [status(thm)], ['63', '64'])).
% 3.42/3.65  thf('66', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['3', '4'])).
% 3.42/3.65  thf(t28_relat_1, axiom,
% 3.42/3.65    (![A:$i]:
% 3.42/3.65     ( ( v1_relat_1 @ A ) =>
% 3.42/3.65       ( ![B:$i]:
% 3.42/3.65         ( ( v1_relat_1 @ B ) =>
% 3.42/3.65           ( r1_tarski @
% 3.42/3.65             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 3.42/3.65             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.42/3.65  thf('67', plain,
% 3.42/3.65      (![X55 : $i, X56 : $i]:
% 3.42/3.65         (~ (v1_relat_1 @ X55)
% 3.42/3.65          | (r1_tarski @ 
% 3.42/3.65             (k6_subset_1 @ (k2_relat_1 @ X56) @ (k2_relat_1 @ X55)) @ 
% 3.42/3.65             (k2_relat_1 @ (k6_subset_1 @ X56 @ X55)))
% 3.42/3.65          | ~ (v1_relat_1 @ X56))),
% 3.42/3.65      inference('cnf', [status(esa)], [t28_relat_1])).
% 3.42/3.65  thf('68', plain,
% 3.42/3.65      (![X38 : $i, X39 : $i]:
% 3.42/3.65         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 3.42/3.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.42/3.65  thf('69', plain,
% 3.42/3.65      (![X38 : $i, X39 : $i]:
% 3.42/3.65         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 3.42/3.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.42/3.65  thf('70', plain,
% 3.42/3.65      (![X55 : $i, X56 : $i]:
% 3.42/3.65         (~ (v1_relat_1 @ X55)
% 3.42/3.65          | (r1_tarski @ 
% 3.42/3.65             (k4_xboole_0 @ (k2_relat_1 @ X56) @ (k2_relat_1 @ X55)) @ 
% 3.42/3.65             (k2_relat_1 @ (k4_xboole_0 @ X56 @ X55)))
% 3.42/3.65          | ~ (v1_relat_1 @ X56))),
% 3.42/3.65      inference('demod', [status(thm)], ['67', '68', '69'])).
% 3.42/3.65  thf('71', plain,
% 3.42/3.65      (![X6 : $i, X8 : $i]:
% 3.42/3.65         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 3.42/3.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.42/3.65  thf('72', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (v1_relat_1 @ X1)
% 3.42/3.65          | ~ (v1_relat_1 @ X0)
% 3.42/3.65          | ~ (r1_tarski @ (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 3.42/3.65               (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 3.42/3.65          | ((k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 3.42/3.65              = (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))),
% 3.42/3.65      inference('sup-', [status(thm)], ['70', '71'])).
% 3.42/3.65  thf('73', plain,
% 3.42/3.65      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 3.42/3.65           (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 3.42/3.65        | ((k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 3.42/3.65            = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 3.42/3.65        | ~ (v1_relat_1 @ sk_B_1)
% 3.42/3.65        | ~ (v1_relat_1 @ sk_A))),
% 3.42/3.65      inference('sup-', [status(thm)], ['66', '72'])).
% 3.42/3.65  thf(cc1_relat_1, axiom,
% 3.42/3.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 3.42/3.65  thf('74', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 3.42/3.65      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.42/3.65  thf('75', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['23', '24'])).
% 3.42/3.65  thf('76', plain,
% 3.42/3.65      (![X50 : $i]:
% 3.42/3.65         (((k3_relat_1 @ X50)
% 3.42/3.65            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 3.42/3.65          | ~ (v1_relat_1 @ X50))),
% 3.42/3.65      inference('cnf', [status(esa)], [d6_relat_1])).
% 3.42/3.65  thf('77', plain,
% 3.42/3.65      ((((k3_relat_1 @ k1_xboole_0)
% 3.42/3.65          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 3.42/3.65        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('sup+', [status(thm)], ['75', '76'])).
% 3.42/3.65  thf('78', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 3.42/3.65      inference('simplify', [status(thm)], ['39'])).
% 3.42/3.65  thf('79', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 3.42/3.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.42/3.65  thf('80', plain,
% 3.42/3.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.42/3.65         (~ (r1_tarski @ X29 @ X30)
% 3.42/3.65          | ~ (r1_tarski @ X31 @ X30)
% 3.42/3.65          | (r1_tarski @ (k2_xboole_0 @ X29 @ X31) @ X30))),
% 3.42/3.65      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.42/3.65  thf('81', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         ((r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ X0)
% 3.42/3.65          | ~ (r1_tarski @ X1 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['79', '80'])).
% 3.42/3.65  thf('82', plain,
% 3.42/3.65      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 3.42/3.65      inference('sup-', [status(thm)], ['78', '81'])).
% 3.42/3.65  thf('83', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['49', '50'])).
% 3.42/3.65  thf('84', plain,
% 3.42/3.65      (![X6 : $i, X8 : $i]:
% 3.42/3.65         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 3.42/3.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.42/3.65  thf('85', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 3.42/3.65          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['83', '84'])).
% 3.42/3.65  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['82', '85'])).
% 3.42/3.65  thf('87', plain,
% 3.42/3.65      ((((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 3.42/3.65        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('demod', [status(thm)], ['77', '86'])).
% 3.42/3.65  thf('88', plain,
% 3.42/3.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.42/3.65        | ((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['74', '87'])).
% 3.42/3.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.42/3.65  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.42/3.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.42/3.65  thf('90', plain, (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('demod', [status(thm)], ['88', '89'])).
% 3.42/3.65  thf('91', plain, (![X42 : $i]: ((v1_relat_1 @ X42) | ~ (v1_xboole_0 @ X42))),
% 3.42/3.65      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.42/3.65  thf('92', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['23', '24'])).
% 3.42/3.65  thf('93', plain,
% 3.42/3.65      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 3.42/3.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.42/3.65  thf(t19_relat_1, axiom,
% 3.42/3.65    (![A:$i,B:$i]:
% 3.42/3.65     ( ( v1_relat_1 @ B ) =>
% 3.42/3.65       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 3.42/3.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 3.42/3.65  thf('94', plain,
% 3.42/3.65      (![X53 : $i, X54 : $i]:
% 3.42/3.65         ((r2_hidden @ (sk_C_2 @ X53) @ (k1_relat_1 @ X53))
% 3.42/3.65          | ~ (r2_hidden @ X54 @ (k2_relat_1 @ X53))
% 3.42/3.65          | ~ (v1_relat_1 @ X53))),
% 3.42/3.65      inference('cnf', [status(esa)], [t19_relat_1])).
% 3.42/3.65  thf('95', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.42/3.65          | ~ (v1_relat_1 @ X0)
% 3.42/3.65          | (r2_hidden @ (sk_C_2 @ X0) @ (k1_relat_1 @ X0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['93', '94'])).
% 3.42/3.65  thf(idempotence_k3_xboole_0, axiom,
% 3.42/3.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 3.42/3.65  thf('96', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.42/3.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.42/3.65  thf('97', plain,
% 3.42/3.65      (![X1 : $i, X3 : $i, X4 : $i]:
% 3.42/3.65         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 3.42/3.65          | ~ (r1_xboole_0 @ X1 @ X4))),
% 3.42/3.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.42/3.65  thf('98', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['96', '97'])).
% 3.42/3.65  thf('99', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         (~ (v1_relat_1 @ X0)
% 3.42/3.65          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.42/3.65          | ~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['95', '98'])).
% 3.42/3.65  thf('100', plain,
% 3.42/3.65      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 3.42/3.65        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.42/3.65        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['92', '99'])).
% 3.42/3.65  thf('101', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['23', '24'])).
% 3.42/3.65  thf(commutativity_k2_tarski, axiom,
% 3.42/3.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.42/3.65  thf('102', plain,
% 3.42/3.65      (![X32 : $i, X33 : $i]:
% 3.42/3.65         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 3.42/3.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.42/3.65  thf(t12_setfam_1, axiom,
% 3.42/3.65    (![A:$i,B:$i]:
% 3.42/3.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.42/3.65  thf('103', plain,
% 3.42/3.65      (![X40 : $i, X41 : $i]:
% 3.42/3.65         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 3.42/3.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.42/3.65  thf('104', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.42/3.65      inference('sup+', [status(thm)], ['102', '103'])).
% 3.42/3.65  thf('105', plain,
% 3.42/3.65      (![X40 : $i, X41 : $i]:
% 3.42/3.65         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 3.42/3.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.42/3.65  thf('106', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.42/3.65      inference('sup+', [status(thm)], ['104', '105'])).
% 3.42/3.65  thf('107', plain,
% 3.42/3.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['14', '17'])).
% 3.42/3.65  thf('108', plain,
% 3.42/3.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.42/3.65      inference('sup+', [status(thm)], ['106', '107'])).
% 3.42/3.65  thf('109', plain,
% 3.42/3.65      (![X1 : $i, X2 : $i]:
% 3.42/3.65         ((r1_xboole_0 @ X1 @ X2)
% 3.42/3.65          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X2)))),
% 3.42/3.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.42/3.65  thf('110', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['96', '97'])).
% 3.42/3.65  thf('111', plain,
% 3.42/3.65      (![X0 : $i, X1 : $i]:
% 3.42/3.65         ((r1_xboole_0 @ X1 @ X0)
% 3.42/3.65          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['109', '110'])).
% 3.42/3.65  thf('112', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         (~ (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 3.42/3.65          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['108', '111'])).
% 3.42/3.65  thf('113', plain,
% 3.42/3.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.42/3.65      inference('sup+', [status(thm)], ['106', '107'])).
% 3.42/3.65  thf('114', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 3.42/3.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.42/3.65  thf('115', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.42/3.65      inference('demod', [status(thm)], ['112', '113', '114'])).
% 3.42/3.65  thf('116', plain,
% 3.42/3.65      (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('demod', [status(thm)], ['88', '89'])).
% 3.42/3.65  thf('117', plain,
% 3.42/3.65      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.42/3.65        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('demod', [status(thm)], ['100', '101', '115', '116'])).
% 3.42/3.65  thf('118', plain,
% 3.42/3.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.42/3.65        | ((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['91', '117'])).
% 3.42/3.65  thf('119', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.42/3.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.42/3.65  thf('120', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.42/3.65      inference('demod', [status(thm)], ['118', '119'])).
% 3.42/3.65  thf('121', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('demod', [status(thm)], ['90', '120'])).
% 3.42/3.65  thf('122', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 3.42/3.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.42/3.65  thf('123', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 3.42/3.65      inference('sup-', [status(thm)], ['3', '4'])).
% 3.42/3.65  thf('124', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 3.42/3.65      inference('demod', [status(thm)], ['90', '120'])).
% 3.42/3.65  thf('125', plain, ((v1_relat_1 @ sk_B_1)),
% 3.42/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.65  thf('126', plain, ((v1_relat_1 @ sk_A)),
% 3.42/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.65  thf('127', plain,
% 3.42/3.65      (((k1_xboole_0)
% 3.42/3.65         = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 3.42/3.65      inference('demod', [status(thm)],
% 3.42/3.65                ['73', '121', '122', '123', '124', '125', '126'])).
% 3.42/3.65  thf('128', plain,
% 3.42/3.65      (![X9 : $i, X10 : $i]:
% 3.42/3.65         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 3.42/3.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.42/3.65  thf('129', plain,
% 3.42/3.65      ((((k1_xboole_0) != (k1_xboole_0))
% 3.42/3.65        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['127', '128'])).
% 3.42/3.65  thf('130', plain,
% 3.42/3.65      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('simplify', [status(thm)], ['129'])).
% 3.42/3.65  thf('131', plain,
% 3.42/3.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.42/3.65         (~ (r1_tarski @ X12 @ X13)
% 3.42/3.65          | (r1_tarski @ X12 @ (k2_xboole_0 @ X14 @ X13)))),
% 3.42/3.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.42/3.65  thf('132', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 3.42/3.65          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['130', '131'])).
% 3.42/3.65  thf('133', plain,
% 3.42/3.65      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup+', [status(thm)], ['65', '132'])).
% 3.42/3.65  thf('134', plain,
% 3.42/3.65      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('demod', [status(thm)], ['36', '37'])).
% 3.42/3.65  thf('135', plain,
% 3.42/3.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.42/3.65         (~ (r1_tarski @ X29 @ X30)
% 3.42/3.65          | ~ (r1_tarski @ X31 @ X30)
% 3.42/3.65          | (r1_tarski @ (k2_xboole_0 @ X29 @ X31) @ X30))),
% 3.42/3.65      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.42/3.65  thf('136', plain,
% 3.42/3.65      (![X0 : $i]:
% 3.42/3.65         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 3.42/3.65           (k3_relat_1 @ sk_B_1))
% 3.42/3.65          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 3.42/3.65      inference('sup-', [status(thm)], ['134', '135'])).
% 3.42/3.65  thf('137', plain,
% 3.42/3.65      ((r1_tarski @ 
% 3.42/3.65        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 3.42/3.65        (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('sup-', [status(thm)], ['133', '136'])).
% 3.42/3.65  thf('138', plain,
% 3.42/3.65      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 3.42/3.65        | ~ (v1_relat_1 @ sk_A))),
% 3.42/3.65      inference('sup+', [status(thm)], ['1', '137'])).
% 3.42/3.65  thf('139', plain, ((v1_relat_1 @ sk_A)),
% 3.42/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.65  thf('140', plain,
% 3.42/3.65      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 3.42/3.65      inference('demod', [status(thm)], ['138', '139'])).
% 3.42/3.65  thf('141', plain, ($false), inference('demod', [status(thm)], ['0', '140'])).
% 3.42/3.65  
% 3.42/3.65  % SZS output end Refutation
% 3.42/3.65  
% 3.42/3.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
