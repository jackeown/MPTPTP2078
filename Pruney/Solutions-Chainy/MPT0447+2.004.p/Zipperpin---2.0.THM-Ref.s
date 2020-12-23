%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OjbyLzpQHU

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:53 EST 2020

% Result     : Theorem 51.69s
% Output     : Refutation 51.69s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 920 expanded)
%              Number of leaves         :   47 ( 313 expanded)
%              Depth                    :   23
%              Number of atoms          : 1486 (7613 expanded)
%              Number of equality atoms :   63 ( 302 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_tarski_type,type,(
    r2_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

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
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X57: $i] :
      ( ( ( k3_relat_1 @ X57 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X59 ) @ ( k1_relat_1 @ X58 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X59 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X59 ) @ ( k1_relat_1 @ X58 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X59 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) )
    | ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
      = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('14',plain,(
    ! [X52: $i,X55: $i] :
      ( ( X55
        = ( k1_relat_1 @ X52 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X55 @ X52 ) @ ( sk_D_1 @ X55 @ X52 ) ) @ X52 )
      | ( r2_hidden @ ( sk_C_2 @ X55 @ X52 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t9_tarski,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ~ ( ( r1_tarski @ C @ B )
            & ~ ( r2_tarski @ C @ B )
            & ~ ( r2_hidden @ C @ B ) )
      & ! [C: $i] :
          ~ ( ( r2_hidden @ C @ B )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ! [E: $i] :
                      ( ( r1_tarski @ E @ C )
                     => ( r2_hidden @ E @ D ) ) ) )
      & ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r1_tarski @ D @ C ) )
         => ( r2_hidden @ D @ B ) )
      & ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X41: $i] :
      ( r2_hidden @ X41 @ ( sk_B_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t9_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('26',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['13','22','23','24','25','26','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('38',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( r1_tarski @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('42',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X57: $i] :
      ( ( ( k3_relat_1 @ X57 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('50',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( r1_tarski @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['56','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_2 ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('69',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( v1_relat_1 @ X62 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X63 ) @ ( k2_relat_1 @ X62 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X63 @ X62 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('70',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('71',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('72',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( v1_relat_1 @ X62 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X63 ) @ ( k2_relat_1 @ X62 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X63 @ X62 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('77',plain,(
    ! [X49: $i] :
      ( ( v1_relat_1 @ X49 )
      | ~ ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('78',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('79',plain,(
    ! [X57: $i] :
      ( ( ( k3_relat_1 @ X57 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('80',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) @ ( k3_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','87'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('89',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('90',plain,(
    ! [X49: $i] :
      ( ( v1_relat_1 @ X49 )
      | ~ ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('91',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('92',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X60 ) @ ( k1_relat_1 @ X60 ) )
      | ~ ( r2_hidden @ X61 @ ( k2_relat_1 @ X60 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','100'])).

thf('102',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','101'])).

thf('103',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('104',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B_2 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('106',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['67','108'])).

thf('110',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('111',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( r1_tarski @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_2 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('116',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('118',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('120',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k3_relat_1 @ sk_B_2 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['118','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('127',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ k1_xboole_0 ) @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['124','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('137',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('140',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('142',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X57: $i] :
      ( ( ( k3_relat_1 @ X57 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['142','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
      = ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('159',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( r1_tarski @ ( k2_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['156','163'])).

thf('165',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['113','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['0','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OjbyLzpQHU
% 0.17/0.37  % Computer   : n015.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 18:23:38 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 51.69/51.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 51.69/51.93  % Solved by: fo/fo7.sh
% 51.69/51.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.69/51.93  % done 60728 iterations in 51.437s
% 51.69/51.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 51.69/51.93  % SZS output start Refutation
% 51.69/51.93  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 51.69/51.93  thf(sk_B_type, type, sk_B: $i > $i).
% 51.69/51.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 51.69/51.93  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 51.69/51.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 51.69/51.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 51.69/51.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.69/51.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 51.69/51.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.69/51.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 51.69/51.93  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 51.69/51.93  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 51.69/51.93  thf(r2_tarski_type, type, r2_tarski: $i > $i > $o).
% 51.69/51.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 51.69/51.93  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 51.69/51.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 51.69/51.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 51.69/51.93  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 51.69/51.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.69/51.93  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 51.69/51.93  thf(sk_A_type, type, sk_A: $i).
% 51.69/51.93  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 51.69/51.93  thf(sk_B_2_type, type, sk_B_2: $i).
% 51.69/51.93  thf(t31_relat_1, conjecture,
% 51.69/51.93    (![A:$i]:
% 51.69/51.93     ( ( v1_relat_1 @ A ) =>
% 51.69/51.93       ( ![B:$i]:
% 51.69/51.93         ( ( v1_relat_1 @ B ) =>
% 51.69/51.93           ( ( r1_tarski @ A @ B ) =>
% 51.69/51.93             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 51.69/51.93  thf(zf_stmt_0, negated_conjecture,
% 51.69/51.93    (~( ![A:$i]:
% 51.69/51.93        ( ( v1_relat_1 @ A ) =>
% 51.69/51.93          ( ![B:$i]:
% 51.69/51.93            ( ( v1_relat_1 @ B ) =>
% 51.69/51.93              ( ( r1_tarski @ A @ B ) =>
% 51.69/51.93                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 51.69/51.93    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 51.69/51.93  thf('0', plain,
% 51.69/51.93      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf(d6_relat_1, axiom,
% 51.69/51.93    (![A:$i]:
% 51.69/51.93     ( ( v1_relat_1 @ A ) =>
% 51.69/51.93       ( ( k3_relat_1 @ A ) =
% 51.69/51.93         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 51.69/51.93  thf('1', plain,
% 51.69/51.93      (![X57 : $i]:
% 51.69/51.93         (((k3_relat_1 @ X57)
% 51.69/51.93            = (k2_xboole_0 @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X57)))
% 51.69/51.93          | ~ (v1_relat_1 @ X57))),
% 51.69/51.93      inference('cnf', [status(esa)], [d6_relat_1])).
% 51.69/51.93  thf(t7_xboole_1, axiom,
% 51.69/51.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 51.69/51.93  thf('2', plain,
% 51.69/51.93      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 51.69/51.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 51.69/51.93  thf('3', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['1', '2'])).
% 51.69/51.93  thf('4', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf(l32_xboole_1, axiom,
% 51.69/51.93    (![A:$i,B:$i]:
% 51.69/51.93     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 51.69/51.93  thf('5', plain,
% 51.69/51.93      (![X9 : $i, X11 : $i]:
% 51.69/51.93         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 51.69/51.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 51.69/51.93  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['4', '5'])).
% 51.69/51.93  thf(t15_relat_1, axiom,
% 51.69/51.93    (![A:$i]:
% 51.69/51.93     ( ( v1_relat_1 @ A ) =>
% 51.69/51.93       ( ![B:$i]:
% 51.69/51.93         ( ( v1_relat_1 @ B ) =>
% 51.69/51.93           ( r1_tarski @
% 51.69/51.93             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 51.69/51.93             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 51.69/51.93  thf('7', plain,
% 51.69/51.93      (![X58 : $i, X59 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X58)
% 51.69/51.93          | (r1_tarski @ 
% 51.69/51.93             (k6_subset_1 @ (k1_relat_1 @ X59) @ (k1_relat_1 @ X58)) @ 
% 51.69/51.93             (k1_relat_1 @ (k6_subset_1 @ X59 @ X58)))
% 51.69/51.93          | ~ (v1_relat_1 @ X59))),
% 51.69/51.93      inference('cnf', [status(esa)], [t15_relat_1])).
% 51.69/51.93  thf(redefinition_k6_subset_1, axiom,
% 51.69/51.93    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 51.69/51.93  thf('8', plain,
% 51.69/51.93      (![X47 : $i, X48 : $i]:
% 51.69/51.93         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 51.69/51.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 51.69/51.93  thf('9', plain,
% 51.69/51.93      (![X47 : $i, X48 : $i]:
% 51.69/51.93         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 51.69/51.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 51.69/51.93  thf('10', plain,
% 51.69/51.93      (![X58 : $i, X59 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X58)
% 51.69/51.93          | (r1_tarski @ 
% 51.69/51.93             (k4_xboole_0 @ (k1_relat_1 @ X59) @ (k1_relat_1 @ X58)) @ 
% 51.69/51.93             (k1_relat_1 @ (k4_xboole_0 @ X59 @ X58)))
% 51.69/51.93          | ~ (v1_relat_1 @ X59))),
% 51.69/51.93      inference('demod', [status(thm)], ['7', '8', '9'])).
% 51.69/51.93  thf(d10_xboole_0, axiom,
% 51.69/51.93    (![A:$i,B:$i]:
% 51.69/51.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 51.69/51.93  thf('11', plain,
% 51.69/51.93      (![X6 : $i, X8 : $i]:
% 51.69/51.93         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 51.69/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.69/51.93  thf('12', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X1)
% 51.69/51.93          | ~ (v1_relat_1 @ X0)
% 51.69/51.93          | ~ (r1_tarski @ (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 51.69/51.93               (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 51.69/51.93          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 51.69/51.93              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0))))),
% 51.69/51.93      inference('sup-', [status(thm)], ['10', '11'])).
% 51.69/51.93  thf('13', plain,
% 51.69/51.93      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ 
% 51.69/51.93           (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)))
% 51.69/51.93        | ((k1_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_2))
% 51.69/51.93            = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)))
% 51.69/51.93        | ~ (v1_relat_1 @ sk_B_2)
% 51.69/51.93        | ~ (v1_relat_1 @ sk_A))),
% 51.69/51.93      inference('sup-', [status(thm)], ['6', '12'])).
% 51.69/51.93  thf(d4_relat_1, axiom,
% 51.69/51.93    (![A:$i,B:$i]:
% 51.69/51.93     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 51.69/51.93       ( ![C:$i]:
% 51.69/51.93         ( ( r2_hidden @ C @ B ) <=>
% 51.69/51.93           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 51.69/51.93  thf('14', plain,
% 51.69/51.93      (![X52 : $i, X55 : $i]:
% 51.69/51.93         (((X55) = (k1_relat_1 @ X52))
% 51.69/51.93          | (r2_hidden @ 
% 51.69/51.93             (k4_tarski @ (sk_C_2 @ X55 @ X52) @ (sk_D_1 @ X55 @ X52)) @ X52)
% 51.69/51.93          | (r2_hidden @ (sk_C_2 @ X55 @ X52) @ X55))),
% 51.69/51.93      inference('cnf', [status(esa)], [d4_relat_1])).
% 51.69/51.93  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 51.69/51.93  thf('15', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 51.69/51.93      inference('cnf', [status(esa)], [t65_xboole_1])).
% 51.69/51.93  thf(t9_tarski, axiom,
% 51.69/51.93    (![A:$i]:
% 51.69/51.93     ( ?[B:$i]:
% 51.69/51.93       ( ( ![C:$i]:
% 51.69/51.93           ( ~( ( r1_tarski @ C @ B ) & ( ~( r2_tarski @ C @ B ) ) & 
% 51.69/51.93                ( ~( r2_hidden @ C @ B ) ) ) ) ) & 
% 51.69/51.93         ( ![C:$i]:
% 51.69/51.93           ( ~( ( r2_hidden @ C @ B ) & 
% 51.69/51.93                ( ![D:$i]:
% 51.69/51.93                  ( ~( ( r2_hidden @ D @ B ) & 
% 51.69/51.93                       ( ![E:$i]:
% 51.69/51.93                         ( ( r1_tarski @ E @ C ) => ( r2_hidden @ E @ D ) ) ) ) ) ) ) ) ) & 
% 51.69/51.93         ( ![C:$i,D:$i]:
% 51.69/51.93           ( ( ( r2_hidden @ C @ B ) & ( r1_tarski @ D @ C ) ) =>
% 51.69/51.93             ( r2_hidden @ D @ B ) ) ) & 
% 51.69/51.93         ( r2_hidden @ A @ B ) ) ))).
% 51.69/51.93  thf('16', plain, (![X41 : $i]: (r2_hidden @ X41 @ (sk_B_1 @ X41))),
% 51.69/51.93      inference('cnf', [status(esa)], [t9_tarski])).
% 51.69/51.93  thf(t3_xboole_0, axiom,
% 51.69/51.93    (![A:$i,B:$i]:
% 51.69/51.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 51.69/51.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 51.69/51.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 51.69/51.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 51.69/51.93  thf('17', plain,
% 51.69/51.93      (![X1 : $i, X3 : $i, X4 : $i]:
% 51.69/51.93         (~ (r2_hidden @ X3 @ X1)
% 51.69/51.93          | ~ (r2_hidden @ X3 @ X4)
% 51.69/51.93          | ~ (r1_xboole_0 @ X1 @ X4))),
% 51.69/51.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 51.69/51.93  thf('18', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (r1_xboole_0 @ (sk_B_1 @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 51.69/51.93      inference('sup-', [status(thm)], ['16', '17'])).
% 51.69/51.93  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 51.69/51.93      inference('sup-', [status(thm)], ['15', '18'])).
% 51.69/51.93  thf('20', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 51.69/51.93          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['14', '19'])).
% 51.69/51.93  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 51.69/51.93      inference('sup-', [status(thm)], ['15', '18'])).
% 51.69/51.93  thf('22', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['20', '21'])).
% 51.69/51.93  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 51.69/51.93  thf('23', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 51.69/51.93      inference('cnf', [status(esa)], [t2_xboole_1])).
% 51.69/51.93  thf('24', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['4', '5'])).
% 51.69/51.93  thf('25', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['20', '21'])).
% 51.69/51.93  thf('26', plain, ((v1_relat_1 @ sk_B_2)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('28', plain,
% 51.69/51.93      (((k1_xboole_0)
% 51.69/51.93         = (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)))),
% 51.69/51.93      inference('demod', [status(thm)],
% 51.69/51.93                ['13', '22', '23', '24', '25', '26', '27'])).
% 51.69/51.93  thf('29', plain,
% 51.69/51.93      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 51.69/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.69/51.93  thf('30', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 51.69/51.93      inference('simplify', [status(thm)], ['29'])).
% 51.69/51.93  thf(t44_xboole_1, axiom,
% 51.69/51.93    (![A:$i,B:$i,C:$i]:
% 51.69/51.93     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 51.69/51.93       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 51.69/51.93  thf('31', plain,
% 51.69/51.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 51.69/51.93         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 51.69/51.93          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 51.69/51.93      inference('cnf', [status(esa)], [t44_xboole_1])).
% 51.69/51.93  thf('32', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['30', '31'])).
% 51.69/51.93  thf(t1_xboole_1, axiom,
% 51.69/51.93    (![A:$i,B:$i,C:$i]:
% 51.69/51.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 51.69/51.93       ( r1_tarski @ A @ C ) ))).
% 51.69/51.93  thf('33', plain,
% 51.69/51.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X15 @ X16)
% 51.69/51.93          | ~ (r1_tarski @ X16 @ X17)
% 51.69/51.93          | (r1_tarski @ X15 @ X17))),
% 51.69/51.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.69/51.93  thf('34', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.93         ((r1_tarski @ X1 @ X2)
% 51.69/51.93          | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['32', '33'])).
% 51.69/51.93  thf('35', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         (~ (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_B_2) @ k1_xboole_0) @ 
% 51.69/51.93             X0)
% 51.69/51.93          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['28', '34'])).
% 51.69/51.93  thf('36', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 51.69/51.93      inference('cnf', [status(esa)], [t2_xboole_1])).
% 51.69/51.93  thf('37', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 51.69/51.93      inference('simplify', [status(thm)], ['29'])).
% 51.69/51.93  thf(t8_xboole_1, axiom,
% 51.69/51.93    (![A:$i,B:$i,C:$i]:
% 51.69/51.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 51.69/51.93       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 51.69/51.93  thf('38', plain,
% 51.69/51.93      (![X29 : $i, X30 : $i, X31 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X29 @ X30)
% 51.69/51.93          | ~ (r1_tarski @ X31 @ X30)
% 51.69/51.93          | (r1_tarski @ (k2_xboole_0 @ X29 @ X31) @ X30))),
% 51.69/51.93      inference('cnf', [status(esa)], [t8_xboole_1])).
% 51.69/51.93  thf('39', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['37', '38'])).
% 51.69/51.93  thf('40', plain,
% 51.69/51.93      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 51.69/51.93      inference('sup-', [status(thm)], ['36', '39'])).
% 51.69/51.93  thf('41', plain,
% 51.69/51.93      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 51.69/51.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 51.69/51.93  thf('42', plain,
% 51.69/51.93      (![X6 : $i, X8 : $i]:
% 51.69/51.93         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 51.69/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.69/51.93  thf('43', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.69/51.93          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['41', '42'])).
% 51.69/51.93  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['40', '43'])).
% 51.69/51.93  thf('45', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         (~ (r1_tarski @ (k1_relat_1 @ sk_B_2) @ X0)
% 51.69/51.93          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 51.69/51.93      inference('demod', [status(thm)], ['35', '44'])).
% 51.69/51.93  thf('46', plain,
% 51.69/51.93      ((~ (v1_relat_1 @ sk_B_2)
% 51.69/51.93        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['3', '45'])).
% 51.69/51.93  thf('47', plain, ((v1_relat_1 @ sk_B_2)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('48', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('demod', [status(thm)], ['46', '47'])).
% 51.69/51.93  thf('49', plain,
% 51.69/51.93      (![X57 : $i]:
% 51.69/51.93         (((k3_relat_1 @ X57)
% 51.69/51.93            = (k2_xboole_0 @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X57)))
% 51.69/51.93          | ~ (v1_relat_1 @ X57))),
% 51.69/51.93      inference('cnf', [status(esa)], [d6_relat_1])).
% 51.69/51.93  thf('50', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 51.69/51.93      inference('simplify', [status(thm)], ['29'])).
% 51.69/51.93  thf(t10_xboole_1, axiom,
% 51.69/51.93    (![A:$i,B:$i,C:$i]:
% 51.69/51.93     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 51.69/51.93  thf('51', plain,
% 51.69/51.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X12 @ X13)
% 51.69/51.93          | (r1_tarski @ X12 @ (k2_xboole_0 @ X14 @ X13)))),
% 51.69/51.93      inference('cnf', [status(esa)], [t10_xboole_1])).
% 51.69/51.93  thf('52', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['50', '51'])).
% 51.69/51.93  thf('53', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['49', '52'])).
% 51.69/51.93  thf('54', plain,
% 51.69/51.93      (![X29 : $i, X30 : $i, X31 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X29 @ X30)
% 51.69/51.93          | ~ (r1_tarski @ X31 @ X30)
% 51.69/51.93          | (r1_tarski @ (k2_xboole_0 @ X29 @ X31) @ X30))),
% 51.69/51.93      inference('cnf', [status(esa)], [t8_xboole_1])).
% 51.69/51.93  thf('55', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X0)
% 51.69/51.93          | (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1) @ 
% 51.69/51.93             (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['53', '54'])).
% 51.69/51.93  thf('56', plain,
% 51.69/51.93      (((r1_tarski @ 
% 51.69/51.93         (k2_xboole_0 @ (k2_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A)) @ 
% 51.69/51.93         (k3_relat_1 @ sk_B_2))
% 51.69/51.93        | ~ (v1_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['48', '55'])).
% 51.69/51.93  thf(commutativity_k2_tarski, axiom,
% 51.69/51.93    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 51.69/51.93  thf('57', plain,
% 51.69/51.93      (![X32 : $i, X33 : $i]:
% 51.69/51.93         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 51.69/51.93      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 51.69/51.93  thf(l51_zfmisc_1, axiom,
% 51.69/51.93    (![A:$i,B:$i]:
% 51.69/51.93     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 51.69/51.93  thf('58', plain,
% 51.69/51.93      (![X36 : $i, X37 : $i]:
% 51.69/51.93         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 51.69/51.93      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.69/51.93  thf('59', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 51.69/51.93      inference('sup+', [status(thm)], ['57', '58'])).
% 51.69/51.93  thf('60', plain,
% 51.69/51.93      (![X36 : $i, X37 : $i]:
% 51.69/51.93         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 51.69/51.93      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.69/51.93  thf('61', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.69/51.93      inference('sup+', [status(thm)], ['59', '60'])).
% 51.69/51.93  thf('62', plain, ((v1_relat_1 @ sk_B_2)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('63', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)) @ 
% 51.69/51.93        (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('demod', [status(thm)], ['56', '61', '62'])).
% 51.69/51.93  thf('64', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['50', '51'])).
% 51.69/51.93  thf('65', plain,
% 51.69/51.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X15 @ X16)
% 51.69/51.93          | ~ (r1_tarski @ X16 @ X17)
% 51.69/51.93          | (r1_tarski @ X15 @ X17))),
% 51.69/51.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.69/51.93  thf('66', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.93         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['64', '65'])).
% 51.69/51.93  thf('67', plain,
% 51.69/51.93      ((r1_tarski @ (k2_relat_1 @ sk_B_2) @ (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['63', '66'])).
% 51.69/51.93  thf('68', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['4', '5'])).
% 51.69/51.93  thf(t28_relat_1, axiom,
% 51.69/51.93    (![A:$i]:
% 51.69/51.93     ( ( v1_relat_1 @ A ) =>
% 51.69/51.93       ( ![B:$i]:
% 51.69/51.93         ( ( v1_relat_1 @ B ) =>
% 51.69/51.93           ( r1_tarski @
% 51.69/51.93             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 51.69/51.93             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 51.69/51.93  thf('69', plain,
% 51.69/51.93      (![X62 : $i, X63 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X62)
% 51.69/51.93          | (r1_tarski @ 
% 51.69/51.93             (k6_subset_1 @ (k2_relat_1 @ X63) @ (k2_relat_1 @ X62)) @ 
% 51.69/51.93             (k2_relat_1 @ (k6_subset_1 @ X63 @ X62)))
% 51.69/51.93          | ~ (v1_relat_1 @ X63))),
% 51.69/51.93      inference('cnf', [status(esa)], [t28_relat_1])).
% 51.69/51.93  thf('70', plain,
% 51.69/51.93      (![X47 : $i, X48 : $i]:
% 51.69/51.93         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 51.69/51.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 51.69/51.93  thf('71', plain,
% 51.69/51.93      (![X47 : $i, X48 : $i]:
% 51.69/51.93         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 51.69/51.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 51.69/51.93  thf('72', plain,
% 51.69/51.93      (![X62 : $i, X63 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X62)
% 51.69/51.93          | (r1_tarski @ 
% 51.69/51.93             (k4_xboole_0 @ (k2_relat_1 @ X63) @ (k2_relat_1 @ X62)) @ 
% 51.69/51.93             (k2_relat_1 @ (k4_xboole_0 @ X63 @ X62)))
% 51.69/51.93          | ~ (v1_relat_1 @ X63))),
% 51.69/51.93      inference('demod', [status(thm)], ['69', '70', '71'])).
% 51.69/51.93  thf('73', plain,
% 51.69/51.93      (((r1_tarski @ 
% 51.69/51.93         (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)) @ 
% 51.69/51.93         (k2_relat_1 @ k1_xboole_0))
% 51.69/51.93        | ~ (v1_relat_1 @ sk_A)
% 51.69/51.93        | ~ (v1_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('sup+', [status(thm)], ['68', '72'])).
% 51.69/51.93  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('75', plain, ((v1_relat_1 @ sk_B_2)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('76', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)) @ 
% 51.69/51.93        (k2_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('demod', [status(thm)], ['73', '74', '75'])).
% 51.69/51.93  thf(cc1_relat_1, axiom,
% 51.69/51.93    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 51.69/51.93  thf('77', plain, (![X49 : $i]: ((v1_relat_1 @ X49) | ~ (v1_xboole_0 @ X49))),
% 51.69/51.93      inference('cnf', [status(esa)], [cc1_relat_1])).
% 51.69/51.93  thf('78', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['20', '21'])).
% 51.69/51.93  thf('79', plain,
% 51.69/51.93      (![X57 : $i]:
% 51.69/51.93         (((k3_relat_1 @ X57)
% 51.69/51.93            = (k2_xboole_0 @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X57)))
% 51.69/51.93          | ~ (v1_relat_1 @ X57))),
% 51.69/51.93      inference('cnf', [status(esa)], [d6_relat_1])).
% 51.69/51.93  thf('80', plain,
% 51.69/51.93      ((((k3_relat_1 @ k1_xboole_0)
% 51.69/51.93          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 51.69/51.93        | ~ (v1_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['78', '79'])).
% 51.69/51.93  thf('81', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['40', '43'])).
% 51.69/51.93  thf('82', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.69/51.93      inference('sup+', [status(thm)], ['59', '60'])).
% 51.69/51.93  thf('83', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['81', '82'])).
% 51.69/51.93  thf('84', plain,
% 51.69/51.93      ((((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 51.69/51.93        | ~ (v1_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('demod', [status(thm)], ['80', '83'])).
% 51.69/51.93  thf('85', plain,
% 51.69/51.93      ((~ (v1_xboole_0 @ k1_xboole_0)
% 51.69/51.93        | ((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['77', '84'])).
% 51.69/51.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 51.69/51.93  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 51.69/51.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 51.69/51.93  thf('87', plain, (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('demod', [status(thm)], ['85', '86'])).
% 51.69/51.93  thf('88', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)) @ 
% 51.69/51.93        (k3_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('demod', [status(thm)], ['76', '87'])).
% 51.69/51.93  thf(t7_xboole_0, axiom,
% 51.69/51.93    (![A:$i]:
% 51.69/51.93     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 51.69/51.93          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 51.69/51.93  thf('89', plain,
% 51.69/51.93      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 51.69/51.93      inference('cnf', [status(esa)], [t7_xboole_0])).
% 51.69/51.93  thf('90', plain, (![X49 : $i]: ((v1_relat_1 @ X49) | ~ (v1_xboole_0 @ X49))),
% 51.69/51.93      inference('cnf', [status(esa)], [cc1_relat_1])).
% 51.69/51.93  thf('91', plain, (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('demod', [status(thm)], ['85', '86'])).
% 51.69/51.93  thf(t19_relat_1, axiom,
% 51.69/51.93    (![A:$i,B:$i]:
% 51.69/51.93     ( ( v1_relat_1 @ B ) =>
% 51.69/51.93       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 51.69/51.93            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 51.69/51.93  thf('92', plain,
% 51.69/51.93      (![X60 : $i, X61 : $i]:
% 51.69/51.93         ((r2_hidden @ (sk_C_3 @ X60) @ (k1_relat_1 @ X60))
% 51.69/51.93          | ~ (r2_hidden @ X61 @ (k2_relat_1 @ X60))
% 51.69/51.93          | ~ (v1_relat_1 @ X60))),
% 51.69/51.93      inference('cnf', [status(esa)], [t19_relat_1])).
% 51.69/51.93  thf('93', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         (~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))
% 51.69/51.93          | ~ (v1_relat_1 @ k1_xboole_0)
% 51.69/51.93          | (r2_hidden @ (sk_C_3 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['91', '92'])).
% 51.69/51.93  thf('94', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['20', '21'])).
% 51.69/51.93  thf('95', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         (~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))
% 51.69/51.93          | ~ (v1_relat_1 @ k1_xboole_0)
% 51.69/51.93          | (r2_hidden @ (sk_C_3 @ k1_xboole_0) @ k1_xboole_0))),
% 51.69/51.93      inference('demod', [status(thm)], ['93', '94'])).
% 51.69/51.93  thf('96', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 51.69/51.93      inference('sup-', [status(thm)], ['15', '18'])).
% 51.69/51.93  thf('97', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ k1_xboole_0)
% 51.69/51.93          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0)))),
% 51.69/51.93      inference('clc', [status(thm)], ['95', '96'])).
% 51.69/51.93  thf('98', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         (~ (v1_xboole_0 @ k1_xboole_0)
% 51.69/51.93          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['90', '97'])).
% 51.69/51.93  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 51.69/51.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 51.69/51.93  thf('100', plain,
% 51.69/51.93      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))),
% 51.69/51.93      inference('demod', [status(thm)], ['98', '99'])).
% 51.69/51.93  thf('101', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['89', '100'])).
% 51.69/51.93  thf('102', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)) @ 
% 51.69/51.93        k1_xboole_0)),
% 51.69/51.93      inference('demod', [status(thm)], ['88', '101'])).
% 51.69/51.93  thf('103', plain,
% 51.69/51.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 51.69/51.93         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 51.69/51.93          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 51.69/51.93      inference('cnf', [status(esa)], [t44_xboole_1])).
% 51.69/51.93  thf('104', plain,
% 51.69/51.93      ((r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 51.69/51.93        (k2_xboole_0 @ (k2_relat_1 @ sk_B_2) @ k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['102', '103'])).
% 51.69/51.93  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['40', '43'])).
% 51.69/51.93  thf('106', plain,
% 51.69/51.93      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('demod', [status(thm)], ['104', '105'])).
% 51.69/51.93  thf('107', plain,
% 51.69/51.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X15 @ X16)
% 51.69/51.93          | ~ (r1_tarski @ X16 @ X17)
% 51.69/51.93          | (r1_tarski @ X15 @ X17))),
% 51.69/51.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.69/51.93  thf('108', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 51.69/51.93          | ~ (r1_tarski @ (k2_relat_1 @ sk_B_2) @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['106', '107'])).
% 51.69/51.93  thf('109', plain,
% 51.69/51.93      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['67', '108'])).
% 51.69/51.93  thf('110', plain,
% 51.69/51.93      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('demod', [status(thm)], ['46', '47'])).
% 51.69/51.93  thf('111', plain,
% 51.69/51.93      (![X29 : $i, X30 : $i, X31 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X29 @ X30)
% 51.69/51.93          | ~ (r1_tarski @ X31 @ X30)
% 51.69/51.93          | (r1_tarski @ (k2_xboole_0 @ X29 @ X31) @ X30))),
% 51.69/51.93      inference('cnf', [status(esa)], [t8_xboole_1])).
% 51.69/51.93  thf('112', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 51.69/51.93           (k3_relat_1 @ sk_B_2))
% 51.69/51.93          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_2)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['110', '111'])).
% 51.69/51.93  thf('113', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 51.69/51.93        (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['109', '112'])).
% 51.69/51.93  thf('114', plain,
% 51.69/51.93      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('demod', [status(thm)], ['46', '47'])).
% 51.69/51.93  thf('115', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['37', '38'])).
% 51.69/51.93  thf('116', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k2_xboole_0 @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A)) @ 
% 51.69/51.93        (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['114', '115'])).
% 51.69/51.93  thf('117', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.69/51.93          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['41', '42'])).
% 51.69/51.93  thf('118', plain,
% 51.69/51.93      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A))
% 51.69/51.93         = (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['116', '117'])).
% 51.69/51.93  thf('119', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['50', '51'])).
% 51.69/51.93  thf('120', plain,
% 51.69/51.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X12 @ X13)
% 51.69/51.93          | (r1_tarski @ X12 @ (k2_xboole_0 @ X14 @ X13)))),
% 51.69/51.93      inference('cnf', [status(esa)], [t10_xboole_1])).
% 51.69/51.93  thf('121', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.93         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['119', '120'])).
% 51.69/51.93  thf('122', plain,
% 51.69/51.93      (![X9 : $i, X11 : $i]:
% 51.69/51.93         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 51.69/51.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 51.69/51.93  thf('123', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.93         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 51.69/51.93           = (k1_xboole_0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['121', '122'])).
% 51.69/51.93  thf('124', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 51.69/51.93           (k2_xboole_0 @ X0 @ (k3_relat_1 @ sk_B_2))) = (k1_xboole_0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['118', '123'])).
% 51.69/51.93  thf('125', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['1', '2'])).
% 51.69/51.93  thf('126', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['50', '51'])).
% 51.69/51.93  thf(t43_xboole_1, axiom,
% 51.69/51.93    (![A:$i,B:$i,C:$i]:
% 51.69/51.93     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 51.69/51.93       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 51.69/51.93  thf('127', plain,
% 51.69/51.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 51.69/51.93         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 51.69/51.93          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 51.69/51.93      inference('cnf', [status(esa)], [t43_xboole_1])).
% 51.69/51.93  thf('128', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 51.69/51.93      inference('sup-', [status(thm)], ['126', '127'])).
% 51.69/51.93  thf('129', plain,
% 51.69/51.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X15 @ X16)
% 51.69/51.93          | ~ (r1_tarski @ X16 @ X17)
% 51.69/51.93          | (r1_tarski @ X15 @ X17))),
% 51.69/51.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.69/51.93  thf('130', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.69/51.93         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 51.69/51.93      inference('sup-', [status(thm)], ['128', '129'])).
% 51.69/51.93  thf('131', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X0)
% 51.69/51.93          | (r1_tarski @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 51.69/51.93             (k3_relat_1 @ X0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['125', '130'])).
% 51.69/51.93  thf('132', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X0)
% 51.69/51.93          | (r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ X1) @ 
% 51.69/51.93             (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['53', '54'])).
% 51.69/51.93  thf('133', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X0)
% 51.69/51.93          | (r1_tarski @ 
% 51.69/51.93             (k2_xboole_0 @ (k2_relat_1 @ X0) @ 
% 51.69/51.93              (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)) @ 
% 51.69/51.93             (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['131', '132'])).
% 51.69/51.93  thf('134', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         ((r1_tarski @ 
% 51.69/51.93           (k2_xboole_0 @ (k2_relat_1 @ X0) @ 
% 51.69/51.93            (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1)) @ 
% 51.69/51.93           (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('simplify', [status(thm)], ['133'])).
% 51.69/51.93  thf('135', plain,
% 51.69/51.93      (((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ k1_xboole_0) @ 
% 51.69/51.93         (k3_relat_1 @ sk_A))
% 51.69/51.93        | ~ (v1_relat_1 @ sk_A))),
% 51.69/51.93      inference('sup+', [status(thm)], ['124', '134'])).
% 51.69/51.93  thf('136', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['40', '43'])).
% 51.69/51.93  thf('137', plain, ((v1_relat_1 @ sk_A)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('138', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))),
% 51.69/51.93      inference('demod', [status(thm)], ['135', '136', '137'])).
% 51.69/51.93  thf('139', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['37', '38'])).
% 51.69/51.93  thf('140', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k2_xboole_0 @ (k3_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 51.69/51.93        (k3_relat_1 @ sk_A))),
% 51.69/51.93      inference('sup-', [status(thm)], ['138', '139'])).
% 51.69/51.93  thf('141', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.69/51.93          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['41', '42'])).
% 51.69/51.93  thf('142', plain,
% 51.69/51.93      (((k2_xboole_0 @ (k3_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 51.69/51.93         = (k3_relat_1 @ sk_A))),
% 51.69/51.93      inference('sup-', [status(thm)], ['140', '141'])).
% 51.69/51.93  thf('143', plain,
% 51.69/51.93      (![X57 : $i]:
% 51.69/51.93         (((k3_relat_1 @ X57)
% 51.69/51.93            = (k2_xboole_0 @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X57)))
% 51.69/51.93          | ~ (v1_relat_1 @ X57))),
% 51.69/51.93      inference('cnf', [status(esa)], [d6_relat_1])).
% 51.69/51.93  thf('144', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['50', '51'])).
% 51.69/51.93  thf('145', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['37', '38'])).
% 51.69/51.93  thf('146', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ 
% 51.69/51.93          (k2_xboole_0 @ X1 @ X0))),
% 51.69/51.93      inference('sup-', [status(thm)], ['144', '145'])).
% 51.69/51.93  thf('147', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.69/51.93      inference('sup+', [status(thm)], ['59', '60'])).
% 51.69/51.93  thf('148', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (r1_tarski @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 51.69/51.93          (k2_xboole_0 @ X1 @ X0))),
% 51.69/51.93      inference('demod', [status(thm)], ['146', '147'])).
% 51.69/51.93  thf('149', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0)) @ 
% 51.69/51.93           (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['143', '148'])).
% 51.69/51.93  thf('150', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.69/51.93      inference('sup+', [status(thm)], ['59', '60'])).
% 51.69/51.93  thf('151', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ 
% 51.69/51.93           (k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('demod', [status(thm)], ['149', '150'])).
% 51.69/51.93  thf('152', plain,
% 51.69/51.93      (((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 51.69/51.93         (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 51.69/51.93        | ~ (v1_relat_1 @ sk_A))),
% 51.69/51.93      inference('sup+', [status(thm)], ['142', '151'])).
% 51.69/51.93  thf('153', plain, ((v1_relat_1 @ sk_A)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('154', plain,
% 51.69/51.93      ((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 51.69/51.93        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 51.69/51.93      inference('demod', [status(thm)], ['152', '153'])).
% 51.69/51.93  thf('155', plain,
% 51.69/51.93      (![X6 : $i, X8 : $i]:
% 51.69/51.93         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 51.69/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.69/51.93  thf('156', plain,
% 51.69/51.93      ((~ (r1_tarski @ 
% 51.69/51.93           (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 51.69/51.93           (k3_relat_1 @ sk_A))
% 51.69/51.93        | ((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 51.69/51.93            = (k3_relat_1 @ sk_A)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['154', '155'])).
% 51.69/51.93  thf('157', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))),
% 51.69/51.93      inference('demod', [status(thm)], ['135', '136', '137'])).
% 51.69/51.93  thf('158', plain,
% 51.69/51.93      (![X0 : $i]:
% 51.69/51.93         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (v1_relat_1 @ X0))),
% 51.69/51.93      inference('sup+', [status(thm)], ['1', '2'])).
% 51.69/51.93  thf('159', plain,
% 51.69/51.93      (![X29 : $i, X30 : $i, X31 : $i]:
% 51.69/51.93         (~ (r1_tarski @ X29 @ X30)
% 51.69/51.93          | ~ (r1_tarski @ X31 @ X30)
% 51.69/51.93          | (r1_tarski @ (k2_xboole_0 @ X29 @ X31) @ X30))),
% 51.69/51.93      inference('cnf', [status(esa)], [t8_xboole_1])).
% 51.69/51.93  thf('160', plain,
% 51.69/51.93      (![X0 : $i, X1 : $i]:
% 51.69/51.93         (~ (v1_relat_1 @ X0)
% 51.69/51.93          | (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 51.69/51.93             (k3_relat_1 @ X0))
% 51.69/51.93          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 51.69/51.93      inference('sup-', [status(thm)], ['158', '159'])).
% 51.69/51.93  thf('161', plain,
% 51.69/51.93      (((r1_tarski @ 
% 51.69/51.93         (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 51.69/51.93         (k3_relat_1 @ sk_A))
% 51.69/51.93        | ~ (v1_relat_1 @ sk_A))),
% 51.69/51.93      inference('sup-', [status(thm)], ['157', '160'])).
% 51.69/51.93  thf('162', plain, ((v1_relat_1 @ sk_A)),
% 51.69/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.69/51.93  thf('163', plain,
% 51.69/51.93      ((r1_tarski @ 
% 51.69/51.93        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 51.69/51.93        (k3_relat_1 @ sk_A))),
% 51.69/51.93      inference('demod', [status(thm)], ['161', '162'])).
% 51.69/51.93  thf('164', plain,
% 51.69/51.93      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 51.69/51.93         = (k3_relat_1 @ sk_A))),
% 51.69/51.93      inference('demod', [status(thm)], ['156', '163'])).
% 51.69/51.93  thf('165', plain,
% 51.69/51.93      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 51.69/51.93      inference('demod', [status(thm)], ['113', '164'])).
% 51.69/51.93  thf('166', plain, ($false), inference('demod', [status(thm)], ['0', '165'])).
% 51.69/51.93  
% 51.69/51.93  % SZS output end Refutation
% 51.69/51.93  
% 51.69/51.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
