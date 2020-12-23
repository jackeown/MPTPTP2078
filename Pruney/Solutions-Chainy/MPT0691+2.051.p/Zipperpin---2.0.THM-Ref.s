%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noo9nLpvjT

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:24 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 275 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          :  876 (2429 expanded)
%              Number of equality atoms :   68 ( 170 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k7_relat_1 @ X30 @ X31 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k7_relat_1 @ X25 @ ( k1_relat_1 @ X24 ) )
        = ( k7_relat_1 @ X25 @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ ( k1_relat_1 @ X25 ) ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k7_relat_1 @ X25 @ ( k1_relat_1 @ X24 ) )
        = ( k7_relat_1 @ X25 @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ ( k1_relat_1 @ X25 ) ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_B ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('16',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('17',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('18',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17','18','19','20'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X19: $i] :
      ( ( ( k9_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('34',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k7_relat_1 @ X25 @ ( k1_relat_1 @ X24 ) )
        = ( k7_relat_1 @ X25 @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ ( k1_relat_1 @ X25 ) ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('37',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) @ X20 )
        = ( k9_relat_1 @ X22 @ X20 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('50',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('55',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X34 @ X33 ) @ X35 )
        = ( k3_xboole_0 @ X33 @ ( k10_relat_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X23: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noo9nLpvjT
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.77  % Solved by: fo/fo7.sh
% 0.51/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.77  % done 331 iterations in 0.307s
% 0.51/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.77  % SZS output start Refutation
% 0.51/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.51/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.51/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.77  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.51/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.51/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.77  thf(t146_funct_1, conjecture,
% 0.51/0.77    (![A:$i,B:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ B ) =>
% 0.51/0.77       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.77         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.51/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.77    (~( ![A:$i,B:$i]:
% 0.51/0.77        ( ( v1_relat_1 @ B ) =>
% 0.51/0.77          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.77            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.51/0.77    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.51/0.77  thf('0', plain,
% 0.51/0.77      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.77  thf(dt_k7_relat_1, axiom,
% 0.51/0.77    (![A:$i,B:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.51/0.77  thf('1', plain,
% 0.51/0.77      (![X17 : $i, X18 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 0.51/0.77      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.51/0.77  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.51/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.77  thf(t71_relat_1, axiom,
% 0.51/0.77    (![A:$i]:
% 0.51/0.77     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.51/0.77       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.51/0.77  thf('3', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.51/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.77  thf(t97_relat_1, axiom,
% 0.51/0.77    (![A:$i,B:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ B ) =>
% 0.51/0.77       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.51/0.77         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.51/0.77  thf('4', plain,
% 0.51/0.77      (![X30 : $i, X31 : $i]:
% 0.51/0.77         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.51/0.77          | ((k7_relat_1 @ X30 @ X31) = (X30))
% 0.51/0.77          | ~ (v1_relat_1 @ X30))),
% 0.51/0.77      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.51/0.77  thf('5', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (~ (r1_tarski @ X0 @ X1)
% 0.51/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.51/0.77          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.51/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.77  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.51/0.77  thf('6', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.51/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.51/0.77  thf('7', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (~ (r1_tarski @ X0 @ X1)
% 0.51/0.77          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.51/0.77      inference('demod', [status(thm)], ['5', '6'])).
% 0.51/0.77  thf('8', plain,
% 0.51/0.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.51/0.77         = (k6_relat_1 @ sk_A))),
% 0.51/0.77      inference('sup-', [status(thm)], ['2', '7'])).
% 0.51/0.77  thf(t189_relat_1, axiom,
% 0.51/0.77    (![A:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ A ) =>
% 0.51/0.77       ( ![B:$i]:
% 0.51/0.77         ( ( v1_relat_1 @ B ) =>
% 0.51/0.77           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.51/0.77             ( k7_relat_1 @
% 0.51/0.77               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.51/0.77  thf('9', plain,
% 0.51/0.77      (![X24 : $i, X25 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X24)
% 0.51/0.77          | ((k7_relat_1 @ X25 @ (k1_relat_1 @ X24))
% 0.51/0.77              = (k7_relat_1 @ X25 @ 
% 0.51/0.77                 (k1_relat_1 @ (k7_relat_1 @ X24 @ (k1_relat_1 @ X25)))))
% 0.51/0.77          | ~ (v1_relat_1 @ X25))),
% 0.51/0.77      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.51/0.77  thf('10', plain,
% 0.51/0.77      (![X24 : $i, X25 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X24)
% 0.51/0.77          | ((k7_relat_1 @ X25 @ (k1_relat_1 @ X24))
% 0.51/0.77              = (k7_relat_1 @ X25 @ 
% 0.51/0.77                 (k1_relat_1 @ (k7_relat_1 @ X24 @ (k1_relat_1 @ X25)))))
% 0.51/0.77          | ~ (v1_relat_1 @ X25))),
% 0.51/0.77      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.51/0.77  thf('11', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (((k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.51/0.77            (k1_relat_1 @ X1))
% 0.51/0.77            = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.51/0.77               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 0.51/0.77          | ~ (v1_relat_1 @ X1)
% 0.51/0.77          | ~ (v1_relat_1 @ X0)
% 0.51/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 0.51/0.77          | ~ (v1_relat_1 @ X1))),
% 0.51/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.77  thf('12', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 0.51/0.77          | ~ (v1_relat_1 @ X0)
% 0.51/0.77          | ~ (v1_relat_1 @ X1)
% 0.51/0.77          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.51/0.77              (k1_relat_1 @ X1))
% 0.51/0.77              = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.51/0.77                 (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))))))),
% 0.51/0.77      inference('simplify', [status(thm)], ['11'])).
% 0.51/0.77  thf('13', plain,
% 0.51/0.77      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.51/0.77        | ((k7_relat_1 @ 
% 0.51/0.77            (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.51/0.77            (k1_relat_1 @ sk_B))
% 0.51/0.77            = (k7_relat_1 @ 
% 0.51/0.77               (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.51/0.77               (k1_relat_1 @ 
% 0.51/0.77                (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))))))
% 0.51/0.77        | ~ (v1_relat_1 @ sk_B)
% 0.51/0.77        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.51/0.77      inference('sup-', [status(thm)], ['8', '12'])).
% 0.51/0.77  thf('14', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.51/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.51/0.77  thf('15', plain,
% 0.51/0.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.51/0.77         = (k6_relat_1 @ sk_A))),
% 0.51/0.77      inference('sup-', [status(thm)], ['2', '7'])).
% 0.51/0.77  thf('16', plain,
% 0.51/0.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.51/0.77         = (k6_relat_1 @ sk_A))),
% 0.51/0.77      inference('sup-', [status(thm)], ['2', '7'])).
% 0.51/0.77  thf('17', plain,
% 0.51/0.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.51/0.77         = (k6_relat_1 @ sk_A))),
% 0.51/0.77      inference('sup-', [status(thm)], ['2', '7'])).
% 0.51/0.77  thf('18', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.51/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.77  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.77  thf('20', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.51/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.51/0.77  thf('21', plain,
% 0.51/0.77      (((k6_relat_1 @ sk_A)
% 0.51/0.77         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.51/0.77            (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.51/0.77      inference('demod', [status(thm)],
% 0.51/0.77                ['13', '14', '15', '16', '17', '18', '19', '20'])).
% 0.51/0.77  thf(t87_relat_1, axiom,
% 0.51/0.77    (![A:$i,B:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ B ) =>
% 0.51/0.77       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.51/0.77  thf('22', plain,
% 0.51/0.77      (![X28 : $i, X29 : $i]:
% 0.51/0.77         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X28 @ X29)) @ X29)
% 0.51/0.77          | ~ (v1_relat_1 @ X28))),
% 0.51/0.77      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.51/0.77  thf('23', plain,
% 0.51/0.77      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 0.51/0.77         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.51/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.51/0.77  thf('24', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.51/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.77  thf('25', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.51/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.51/0.77  thf('26', plain,
% 0.51/0.77      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.51/0.77  thf('27', plain,
% 0.51/0.77      (![X28 : $i, X29 : $i]:
% 0.51/0.77         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X28 @ X29)) @ X29)
% 0.51/0.77          | ~ (v1_relat_1 @ X28))),
% 0.51/0.77      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.51/0.77  thf(d10_xboole_0, axiom,
% 0.51/0.77    (![A:$i,B:$i]:
% 0.51/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.77  thf('28', plain,
% 0.51/0.77      (![X1 : $i, X3 : $i]:
% 0.51/0.77         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.51/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.77  thf('29', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X1)
% 0.51/0.77          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.51/0.77          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.51/0.77      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.77  thf('30', plain,
% 0.51/0.77      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.77      inference('sup-', [status(thm)], ['26', '29'])).
% 0.51/0.77  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.77  thf('32', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.51/0.77  thf(t146_relat_1, axiom,
% 0.51/0.77    (![A:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ A ) =>
% 0.51/0.77       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.51/0.77  thf('33', plain,
% 0.51/0.77      (![X19 : $i]:
% 0.51/0.77         (((k9_relat_1 @ X19 @ (k1_relat_1 @ X19)) = (k2_relat_1 @ X19))
% 0.51/0.77          | ~ (v1_relat_1 @ X19))),
% 0.51/0.77      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.51/0.77  thf('34', plain,
% 0.51/0.77      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.51/0.77          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('sup+', [status(thm)], ['32', '33'])).
% 0.51/0.77  thf('35', plain,
% 0.51/0.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.51/0.77         = (k6_relat_1 @ sk_A))),
% 0.51/0.77      inference('sup-', [status(thm)], ['2', '7'])).
% 0.51/0.77  thf('36', plain,
% 0.51/0.77      (![X24 : $i, X25 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X24)
% 0.51/0.77          | ((k7_relat_1 @ X25 @ (k1_relat_1 @ X24))
% 0.51/0.77              = (k7_relat_1 @ X25 @ 
% 0.51/0.77                 (k1_relat_1 @ (k7_relat_1 @ X24 @ (k1_relat_1 @ X25)))))
% 0.51/0.77          | ~ (v1_relat_1 @ X25))),
% 0.51/0.77      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.51/0.77  thf('37', plain,
% 0.51/0.77      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.51/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.77  thf('38', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.51/0.77      inference('simplify', [status(thm)], ['37'])).
% 0.51/0.77  thf(t162_relat_1, axiom,
% 0.51/0.77    (![A:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ A ) =>
% 0.51/0.77       ( ![B:$i,C:$i]:
% 0.51/0.77         ( ( r1_tarski @ B @ C ) =>
% 0.51/0.77           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.51/0.77             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.51/0.77  thf('39', plain,
% 0.51/0.77      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.77         (~ (r1_tarski @ X20 @ X21)
% 0.51/0.77          | ((k9_relat_1 @ (k7_relat_1 @ X22 @ X21) @ X20)
% 0.51/0.77              = (k9_relat_1 @ X22 @ X20))
% 0.51/0.77          | ~ (v1_relat_1 @ X22))),
% 0.51/0.77      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.51/0.77  thf('40', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X1)
% 0.51/0.77          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.51/0.77              = (k9_relat_1 @ X1 @ X0)))),
% 0.51/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.77  thf('41', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (((k9_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.51/0.77            (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 0.51/0.77            = (k9_relat_1 @ X1 @ 
% 0.51/0.77               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 0.51/0.77          | ~ (v1_relat_1 @ X1)
% 0.51/0.77          | ~ (v1_relat_1 @ X0)
% 0.51/0.77          | ~ (v1_relat_1 @ X1))),
% 0.51/0.77      inference('sup+', [status(thm)], ['36', '40'])).
% 0.51/0.77  thf('42', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X0)
% 0.51/0.77          | ~ (v1_relat_1 @ X1)
% 0.51/0.77          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.51/0.77              (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 0.51/0.77              = (k9_relat_1 @ X1 @ 
% 0.51/0.77                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))))),
% 0.51/0.77      inference('simplify', [status(thm)], ['41'])).
% 0.51/0.77  thf('43', plain,
% 0.51/0.77      ((((k9_relat_1 @ 
% 0.51/0.77          (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))) @ 
% 0.51/0.77          (k1_relat_1 @ (k6_relat_1 @ sk_A)))
% 0.51/0.77          = (k9_relat_1 @ sk_B @ 
% 0.51/0.77             (k1_relat_1 @ 
% 0.51/0.77              (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))))
% 0.51/0.77        | ~ (v1_relat_1 @ sk_B)
% 0.51/0.77        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.51/0.77      inference('sup+', [status(thm)], ['35', '42'])).
% 0.51/0.77  thf('44', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.51/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.77  thf('45', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.51/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.77  thf('46', plain,
% 0.51/0.77      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.51/0.77         = (k6_relat_1 @ sk_A))),
% 0.51/0.77      inference('sup-', [status(thm)], ['2', '7'])).
% 0.51/0.77  thf('47', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.51/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.77  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.77  thf('49', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.51/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.51/0.77  thf('50', plain,
% 0.51/0.77      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.51/0.77         = (k9_relat_1 @ sk_B @ sk_A))),
% 0.51/0.77      inference('demod', [status(thm)],
% 0.51/0.77                ['43', '44', '45', '46', '47', '48', '49'])).
% 0.51/0.77  thf('51', plain,
% 0.51/0.77      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('demod', [status(thm)], ['34', '50'])).
% 0.51/0.77  thf('52', plain,
% 0.51/0.77      ((~ (v1_relat_1 @ sk_B)
% 0.51/0.77        | ((k9_relat_1 @ sk_B @ sk_A)
% 0.51/0.77            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.51/0.77      inference('sup-', [status(thm)], ['1', '51'])).
% 0.51/0.77  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.77  thf('54', plain,
% 0.51/0.77      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('demod', [status(thm)], ['52', '53'])).
% 0.51/0.77  thf(t139_funct_1, axiom,
% 0.51/0.77    (![A:$i,B:$i,C:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ C ) =>
% 0.51/0.77       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.51/0.77         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.51/0.77  thf('55', plain,
% 0.51/0.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.77         (((k10_relat_1 @ (k7_relat_1 @ X34 @ X33) @ X35)
% 0.51/0.77            = (k3_xboole_0 @ X33 @ (k10_relat_1 @ X34 @ X35)))
% 0.51/0.77          | ~ (v1_relat_1 @ X34))),
% 0.51/0.77      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.51/0.77  thf(t169_relat_1, axiom,
% 0.51/0.77    (![A:$i]:
% 0.51/0.77     ( ( v1_relat_1 @ A ) =>
% 0.51/0.77       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.51/0.77  thf('56', plain,
% 0.51/0.77      (![X23 : $i]:
% 0.51/0.77         (((k10_relat_1 @ X23 @ (k2_relat_1 @ X23)) = (k1_relat_1 @ X23))
% 0.51/0.77          | ~ (v1_relat_1 @ X23))),
% 0.51/0.77      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.51/0.77  thf('57', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (((k3_xboole_0 @ X0 @ 
% 0.51/0.77            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.51/0.77            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.51/0.77          | ~ (v1_relat_1 @ X1)
% 0.51/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.51/0.77      inference('sup+', [status(thm)], ['55', '56'])).
% 0.51/0.77  thf('58', plain,
% 0.51/0.77      (![X17 : $i, X18 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 0.51/0.77      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.51/0.77  thf('59', plain,
% 0.51/0.77      (![X0 : $i, X1 : $i]:
% 0.51/0.77         (~ (v1_relat_1 @ X1)
% 0.51/0.77          | ((k3_xboole_0 @ X0 @ 
% 0.51/0.77              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.51/0.77              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.51/0.77      inference('clc', [status(thm)], ['57', '58'])).
% 0.51/0.77  thf('60', plain,
% 0.51/0.77      ((((k3_xboole_0 @ sk_A @ 
% 0.51/0.77          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.77      inference('sup+', [status(thm)], ['54', '59'])).
% 0.51/0.77  thf('61', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.51/0.77  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.77  thf('63', plain,
% 0.51/0.77      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77         = (sk_A))),
% 0.51/0.77      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.51/0.77  thf(t100_xboole_1, axiom,
% 0.51/0.77    (![A:$i,B:$i]:
% 0.51/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.77  thf('64', plain,
% 0.51/0.77      (![X7 : $i, X8 : $i]:
% 0.51/0.77         ((k4_xboole_0 @ X7 @ X8)
% 0.51/0.77           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.51/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.77  thf('65', plain,
% 0.51/0.77      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.51/0.77      inference('sup+', [status(thm)], ['63', '64'])).
% 0.51/0.77  thf('66', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.51/0.77      inference('simplify', [status(thm)], ['37'])).
% 0.51/0.77  thf(l32_xboole_1, axiom,
% 0.51/0.77    (![A:$i,B:$i]:
% 0.51/0.77     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.77  thf('67', plain,
% 0.51/0.77      (![X4 : $i, X6 : $i]:
% 0.51/0.77         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.51/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.77  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.77      inference('sup-', [status(thm)], ['66', '67'])).
% 0.51/0.77  thf(idempotence_k3_xboole_0, axiom,
% 0.51/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.51/0.77  thf('69', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.51/0.77      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.51/0.77  thf('70', plain,
% 0.51/0.77      (![X7 : $i, X8 : $i]:
% 0.51/0.77         ((k4_xboole_0 @ X7 @ X8)
% 0.51/0.77           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.51/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.77  thf('71', plain,
% 0.51/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.77      inference('sup+', [status(thm)], ['69', '70'])).
% 0.51/0.77  thf('72', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.77      inference('sup+', [status(thm)], ['68', '71'])).
% 0.51/0.77  thf('73', plain,
% 0.51/0.77      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.51/0.77         = (k1_xboole_0))),
% 0.51/0.77      inference('demod', [status(thm)], ['65', '72'])).
% 0.51/0.77  thf('74', plain,
% 0.51/0.77      (![X4 : $i, X5 : $i]:
% 0.51/0.77         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.51/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.77  thf('75', plain,
% 0.51/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.51/0.77        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.51/0.77      inference('sup-', [status(thm)], ['73', '74'])).
% 0.51/0.77  thf('76', plain,
% 0.51/0.77      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.77      inference('simplify', [status(thm)], ['75'])).
% 0.51/0.77  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.51/0.77  
% 0.51/0.77  % SZS output end Refutation
% 0.51/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
