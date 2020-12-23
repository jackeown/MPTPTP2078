%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YBpK5dJCcX

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:34 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 170 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   22
%              Number of atoms          : 1016 (2473 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t158_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_A @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X5 @ X6 ) @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X5 @ X6 ) @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ sk_B @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ sk_B @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YBpK5dJCcX
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 270 iterations in 0.213s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.67  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(t158_relat_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ C ) =>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( v1_relat_1 @ D ) =>
% 0.45/0.67           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.45/0.67             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.67        ( ( v1_relat_1 @ C ) =>
% 0.45/0.67          ( ![D:$i]:
% 0.45/0.67            ( ( v1_relat_1 @ D ) =>
% 0.45/0.67              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.45/0.67                ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t158_relat_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.45/0.67          (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d3_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf(t143_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ C ) =>
% 0.45/0.67       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.67         ( ?[D:$i]:
% 0.45/0.67           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.67             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.67             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X1)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X0 @ X2)
% 0.45/0.67          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (sk_D @ X0 @ sk_A @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['3', '6'])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ (k1_relat_1 @ X7))
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X1)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.67             (k1_relat_1 @ X1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X5 @ X6) @ X6) @ X7)
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X1)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (k4_tarski @ 
% 0.45/0.67              (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.67              (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.67             X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X4 @ X5)
% 0.45/0.67          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ X7)
% 0.45/0.67          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X7))
% 0.45/0.67          | (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.45/0.67             (k9_relat_1 @ X0 @ X3))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.45/0.67               (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3))),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.67         (~ (r2_hidden @ 
% 0.45/0.67             (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3)
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.45/0.67               (k1_relat_1 @ X0))
% 0.45/0.67          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.45/0.67             (k9_relat_1 @ X0 @ X3))
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.45/0.67             (k9_relat_1 @ X0 @ X3))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3))),
% 0.45/0.67      inference('sup-', [status(thm)], ['10', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.67         (~ (r2_hidden @ 
% 0.45/0.67             (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ X3)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.45/0.67             (k9_relat_1 @ X0 @ X3))
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.45/0.67             (k9_relat_1 @ X0 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['7', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.45/0.67           (k9_relat_1 @ X0 @ sk_B))
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (sk_D @ X0 @ sk_B @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r2_hidden @ 
% 0.45/0.67           (sk_D @ X0 @ sk_B @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ sk_B)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.45/0.67           (k9_relat_1 @ X0 @ sk_B))
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ (k1_relat_1 @ X7))
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (sk_D @ X0 @ sk_B @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ 
% 0.45/0.67             (k1_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r2_hidden @ 
% 0.45/0.67           (sk_D @ X0 @ sk_B @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ 
% 0.45/0.67           (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['26'])).
% 0.45/0.67  thf('28', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t25_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( v1_relat_1 @ B ) =>
% 0.45/0.67           ( ( r1_tarski @ A @ B ) =>
% 0.45/0.67             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.45/0.67               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X8)
% 0.45/0.67          | (r1_tarski @ (k1_relat_1 @ X9) @ (k1_relat_1 @ X8))
% 0.45/0.67          | ~ (r1_tarski @ X9 @ X8)
% 0.45/0.67          | ~ (v1_relat_1 @ X9))),
% 0.45/0.67      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C_1)
% 0.45/0.67        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D_1))
% 0.45/0.67        | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.67  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D_1))),
% 0.45/0.67      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X0 @ X2)
% 0.45/0.67          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.45/0.67          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ sk_C_1)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (sk_D @ sk_C_1 @ sk_B @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67             (k1_relat_1 @ sk_D_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['27', '35'])).
% 0.45/0.67  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (sk_D @ sk_C_1 @ sk_B @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67             (k1_relat_1 @ sk_D_1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.45/0.67           (k9_relat_1 @ X0 @ sk_B))
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X5 @ X6) @ X6) @ X7)
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (k4_tarski @ 
% 0.45/0.67              (sk_D @ X0 @ sk_B @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ 
% 0.45/0.67              (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ 
% 0.45/0.67             X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r2_hidden @ 
% 0.45/0.67           (k4_tarski @ 
% 0.45/0.67            (sk_D @ X0 @ sk_B @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ 
% 0.45/0.67            (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ 
% 0.45/0.67           X0)
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.67  thf('43', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X0 @ X2)
% 0.45/0.67          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ sk_C_1)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (k4_tarski @ 
% 0.45/0.67              (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67               (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67              (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67             sk_D_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['42', '45'])).
% 0.45/0.67  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (k4_tarski @ 
% 0.45/0.67              (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67               (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67              (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67             sk_D_1))),
% 0.45/0.67      inference('demod', [status(thm)], ['46', '47'])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X4 @ X5)
% 0.45/0.67          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ X7)
% 0.45/0.67          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X7))
% 0.45/0.67          | (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.45/0.67          | ~ (v1_relat_1 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ sk_D_1)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.45/0.67             (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67                (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67               (k1_relat_1 @ sk_D_1))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67                (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67               X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.67  thf('51', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.45/0.67             (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67                (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67               (k1_relat_1 @ sk_D_1))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67                (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67               X1))),
% 0.45/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67                (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67               X1)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.45/0.67             (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['38', '52'])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.45/0.67           (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.67          | ~ (r2_hidden @ 
% 0.45/0.67               (sk_D @ sk_C_1 @ sk_B @ 
% 0.45/0.67                (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))) @ 
% 0.45/0.67               X1)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ sk_C_1)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.45/0.67             (k9_relat_1 @ sk_D_1 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['23', '54'])).
% 0.45/0.67  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.45/0.67             (k9_relat_1 @ sk_D_1 @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('58', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.45/0.67           (k9_relat_1 @ sk_D_1 @ sk_B))
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['57'])).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.45/0.67         (k9_relat_1 @ sk_D_1 @ sk_B))
% 0.45/0.67        | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.45/0.67           (k9_relat_1 @ sk_D_1 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.45/0.67      inference('simplify', [status(thm)], ['60'])).
% 0.45/0.67  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
