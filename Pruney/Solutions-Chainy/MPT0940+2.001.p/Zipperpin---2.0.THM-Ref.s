%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HPz5wUOSQO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HPz5wUOSQO
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 36 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.49  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.49  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(t5_wellord2, conjecture, (![A:$i]: ( v4_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]: ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t5_wellord2])).
% 0.20/0.49  thf('0', plain, (~ (v4_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d1_wellord2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.49         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.49           ( ![C:$i,D:$i]:
% 0.20/0.49             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.49               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.49                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((X5) != (k1_wellord2 @ X4))
% 0.20/0.49          | ((k3_relat_1 @ X5) = (X4))
% 0.20/0.49          | ~ (v1_relat_1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X4 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X4))
% 0.20/0.49          | ((k3_relat_1 @ (k1_wellord2 @ X4)) = (X4)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.49  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.49  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('4', plain, (![X4 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X4)) = (X4))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(d12_relat_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( v4_relat_2 @ A ) <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X3 : $i]:
% 0.20/0.49         (~ (r4_relat_2 @ X3 @ (k3_relat_1 @ X3))
% 0.20/0.49          | (v4_relat_2 @ X3)
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d12_relat_2])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(d4_relat_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( r4_relat_2 @ A @ B ) <=>
% 0.20/0.49           ( ![C:$i,D:$i]:
% 0.20/0.49             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.20/0.49                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.20/0.49                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) =>
% 0.20/0.49               ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.20/0.49          | (r4_relat_2 @ X9 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D_1 @ X8 @ X9) @ X8)
% 0.20/0.49          | (r4_relat_2 @ X9 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X8 @ X9) @ (sk_C_1 @ X8 @ X9)) @ 
% 0.20/0.49           X9)
% 0.20/0.49          | (r4_relat_2 @ X9 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (((X5) != (k1_wellord2 @ X4))
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.49          | ~ (r2_hidden @ X7 @ X4)
% 0.20/0.49          | (r1_tarski @ X6 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X5)
% 0.20/0.49          | ~ (v1_relat_1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X4))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ (k1_wellord2 @ X4))
% 0.20/0.49          | (r1_tarski @ X6 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X7 @ X4)
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X4))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ (k1_wellord2 @ X4))
% 0.20/0.49          | (r1_tarski @ X6 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X7 @ X4)
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X4))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.20/0.49          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_C_1 @ X1 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '15'])).
% 0.20/0.49  thf('17', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.20/0.49          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_C_1 @ X1 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '18'])).
% 0.20/0.49  thf('20', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_C_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '22'])).
% 0.20/0.49  thf('24', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_C_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49           (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D_1 @ X8 @ X9) @ X8)
% 0.20/0.49          | (r4_relat_2 @ X9 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.20/0.49          | (r4_relat_2 @ X9 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X8 @ X9) @ (sk_D_1 @ X8 @ X9)) @ 
% 0.20/0.49           X9)
% 0.20/0.49          | (r4_relat_2 @ X9 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ (k1_wellord2 @ X4))
% 0.20/0.49          | (r1_tarski @ X6 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X7 @ X4)
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X4))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_D_1 @ X1 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X1)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_D_1 @ X1 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | ~ (r2_hidden @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.49  thf('35', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | ~ (r2_hidden @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_D_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '37'])).
% 0.20/0.49  thf('39', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r1_tarski @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49             (sk_D_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49           (sk_D_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | ~ (r1_tarski @ (sk_D_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.20/0.49               (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | ((sk_D_1 @ X0 @ (k1_wellord2 @ X0))
% 0.20/0.49              = (sk_C_1 @ X0 @ (k1_wellord2 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | ((sk_D_1 @ X0 @ (k1_wellord2 @ X0))
% 0.20/0.49              = (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_D_1 @ X0 @ (k1_wellord2 @ X0))
% 0.20/0.49            = (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (((sk_C_1 @ X8 @ X9) != (sk_D_1 @ X8 @ X9))
% 0.20/0.49          | (r4_relat_2 @ X9 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_C_1 @ X0 @ (k1_wellord2 @ X0))
% 0.20/0.49            != (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_C_1 @ X0 @ (k1_wellord2 @ X0))
% 0.20/0.49            != (sk_C_1 @ X0 @ (k1_wellord2 @ X0)))
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.49          | (r4_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain, (![X0 : $i]: (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.49  thf('51', plain, (![X0 : $i]: (v4_relat_2 @ (k1_wellord2 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '50'])).
% 0.20/0.49  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
