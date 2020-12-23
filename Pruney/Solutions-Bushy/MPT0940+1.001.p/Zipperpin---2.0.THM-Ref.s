%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0940+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0u3H9VqHIk

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:45 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 (  92 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   19
%              Number of atoms          :  751 (1014 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t5_wellord2,conjecture,(
    ! [A: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( v4_relat_2 @ ( k1_wellord2 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t5_wellord2])).

thf('0',plain,(
    ~ ( v4_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5
       != ( k1_wellord2 @ X4 ) )
      | ( ( k3_relat_1 @ X5 )
        = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X4 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X4 ) )
        = X4 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d12_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ~ ( r4_relat_2 @ X3 @ ( k3_relat_1 @ X3 ) )
      | ( v4_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d4_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r4_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) )
             => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r4_relat_2 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X9 ) @ X8 )
      | ( r4_relat_2 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X8 @ X9 ) @ ( sk_C_1 @ X8 @ X9 ) ) @ X9 )
      | ( r4_relat_2 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5
       != ( k1_wellord2 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k1_wellord2 @ X4 ) )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X6 @ X4 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('15',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k1_wellord2 @ X4 ) )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X6 @ X4 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X9 ) @ X8 )
      | ( r4_relat_2 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r4_relat_2 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X8 @ X9 ) @ ( sk_D_1 @ X8 @ X9 ) ) @ X9 )
      | ( r4_relat_2 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('30',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ ( k1_wellord2 @ X4 ) )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X6 @ X4 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) )
        = ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) )
        = ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) )
        = ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( sk_C_1 @ X8 @ X9 )
       != ( sk_D_1 @ X8 @ X9 ) )
      | ( r4_relat_2 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) )
       != ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) )
       != ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).


%------------------------------------------------------------------------------
