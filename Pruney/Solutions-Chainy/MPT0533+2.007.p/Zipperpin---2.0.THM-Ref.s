%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nHyooXKMsO

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:45 EST 2020

% Result     : Theorem 6.79s
% Output     : Refutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  700 ( 992 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X11 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k8_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X9 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X4 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k8_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X9 @ X5 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t133_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t133_relat_1])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X11 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X17 @ X18 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    r1_tarski @ sk_C_2 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k8_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_2 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) ) @ ( k8_relat_1 @ X2 @ sk_D_2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) ) @ ( k8_relat_1 @ X2 @ sk_D_2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_2 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X10 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('40',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_2 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nHyooXKMsO
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 6.79/7.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.79/7.01  % Solved by: fo/fo7.sh
% 6.79/7.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.79/7.01  % done 3392 iterations in 6.551s
% 6.79/7.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.79/7.01  % SZS output start Refutation
% 6.79/7.01  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.79/7.01  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.79/7.01  thf(sk_A_type, type, sk_A: $i).
% 6.79/7.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.79/7.01  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 6.79/7.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.79/7.01  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.79/7.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.79/7.01  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 6.79/7.01  thf(sk_D_2_type, type, sk_D_2: $i).
% 6.79/7.01  thf(sk_B_type, type, sk_B: $i).
% 6.79/7.01  thf(dt_k8_relat_1, axiom,
% 6.79/7.01    (![A:$i,B:$i]:
% 6.79/7.01     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 6.79/7.01  thf('0', plain,
% 6.79/7.01      (![X15 : $i, X16 : $i]:
% 6.79/7.01         ((v1_relat_1 @ (k8_relat_1 @ X15 @ X16)) | ~ (v1_relat_1 @ X16))),
% 6.79/7.01      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 6.79/7.01  thf('1', plain,
% 6.79/7.01      (![X15 : $i, X16 : $i]:
% 6.79/7.01         ((v1_relat_1 @ (k8_relat_1 @ X15 @ X16)) | ~ (v1_relat_1 @ X16))),
% 6.79/7.01      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 6.79/7.01  thf(d3_relat_1, axiom,
% 6.79/7.01    (![A:$i]:
% 6.79/7.01     ( ( v1_relat_1 @ A ) =>
% 6.79/7.01       ( ![B:$i]:
% 6.79/7.01         ( ( r1_tarski @ A @ B ) <=>
% 6.79/7.01           ( ![C:$i,D:$i]:
% 6.79/7.01             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 6.79/7.01               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 6.79/7.01  thf('2', plain,
% 6.79/7.01      (![X10 : $i, X11 : $i]:
% 6.79/7.01         ((r2_hidden @ 
% 6.79/7.01           (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X11)
% 6.79/7.01          | (r1_tarski @ X11 @ X10)
% 6.79/7.01          | ~ (v1_relat_1 @ X11))),
% 6.79/7.01      inference('cnf', [status(esa)], [d3_relat_1])).
% 6.79/7.01  thf(d12_relat_1, axiom,
% 6.79/7.01    (![A:$i,B:$i]:
% 6.79/7.01     ( ( v1_relat_1 @ B ) =>
% 6.79/7.01       ( ![C:$i]:
% 6.79/7.01         ( ( v1_relat_1 @ C ) =>
% 6.79/7.01           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 6.79/7.01             ( ![D:$i,E:$i]:
% 6.79/7.01               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 6.79/7.01                 ( ( r2_hidden @ E @ A ) & 
% 6.79/7.01                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 6.79/7.01  thf('3', plain,
% 6.79/7.01      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X4)
% 6.79/7.01          | ((X4) != (k8_relat_1 @ X5 @ X6))
% 6.79/7.01          | (r2_hidden @ X9 @ X5)
% 6.79/7.01          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X4)
% 6.79/7.01          | ~ (v1_relat_1 @ X6))),
% 6.79/7.01      inference('cnf', [status(esa)], [d12_relat_1])).
% 6.79/7.01  thf('4', plain,
% 6.79/7.01      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X6)
% 6.79/7.01          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k8_relat_1 @ X5 @ X6))
% 6.79/7.01          | (r2_hidden @ X9 @ X5)
% 6.79/7.01          | ~ (v1_relat_1 @ (k8_relat_1 @ X5 @ X6)))),
% 6.79/7.01      inference('simplify', [status(thm)], ['3'])).
% 6.79/7.01  thf('5', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 6.79/7.01          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 6.79/7.01          | (r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 6.79/7.01          | ~ (v1_relat_1 @ X0))),
% 6.79/7.01      inference('sup-', [status(thm)], ['2', '4'])).
% 6.79/7.01  thf('6', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X0)
% 6.79/7.01          | (r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 6.79/7.01          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 6.79/7.01      inference('simplify', [status(thm)], ['5'])).
% 6.79/7.01  thf('7', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X0)
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 6.79/7.01          | (r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 6.79/7.01          | ~ (v1_relat_1 @ X0))),
% 6.79/7.01      inference('sup-', [status(thm)], ['1', '6'])).
% 6.79/7.01  thf('8', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         ((r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 6.79/7.01          | ~ (v1_relat_1 @ X0))),
% 6.79/7.01      inference('simplify', [status(thm)], ['7'])).
% 6.79/7.01  thf(t133_relat_1, conjecture,
% 6.79/7.01    (![A:$i,B:$i,C:$i]:
% 6.79/7.01     ( ( v1_relat_1 @ C ) =>
% 6.79/7.01       ( ![D:$i]:
% 6.79/7.01         ( ( v1_relat_1 @ D ) =>
% 6.79/7.01           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 6.79/7.01             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 6.79/7.01  thf(zf_stmt_0, negated_conjecture,
% 6.79/7.01    (~( ![A:$i,B:$i,C:$i]:
% 6.79/7.01        ( ( v1_relat_1 @ C ) =>
% 6.79/7.01          ( ![D:$i]:
% 6.79/7.01            ( ( v1_relat_1 @ D ) =>
% 6.79/7.01              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 6.79/7.01                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 6.79/7.01    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 6.79/7.01  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 6.79/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.01  thf(d3_tarski, axiom,
% 6.79/7.01    (![A:$i,B:$i]:
% 6.79/7.01     ( ( r1_tarski @ A @ B ) <=>
% 6.79/7.01       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.79/7.01  thf('10', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (r2_hidden @ X0 @ X1)
% 6.79/7.01          | (r2_hidden @ X0 @ X2)
% 6.79/7.01          | ~ (r1_tarski @ X1 @ X2))),
% 6.79/7.01      inference('cnf', [status(esa)], [d3_tarski])).
% 6.79/7.01  thf('11', plain,
% 6.79/7.01      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 6.79/7.01      inference('sup-', [status(thm)], ['9', '10'])).
% 6.79/7.01  thf('12', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X0)
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 6.79/7.01          | (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B))),
% 6.79/7.01      inference('sup-', [status(thm)], ['8', '11'])).
% 6.79/7.01  thf('13', plain,
% 6.79/7.01      (![X15 : $i, X16 : $i]:
% 6.79/7.01         ((v1_relat_1 @ (k8_relat_1 @ X15 @ X16)) | ~ (v1_relat_1 @ X16))),
% 6.79/7.01      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 6.79/7.01  thf('14', plain,
% 6.79/7.01      (![X10 : $i, X11 : $i]:
% 6.79/7.01         ((r2_hidden @ 
% 6.79/7.01           (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X11)
% 6.79/7.01          | (r1_tarski @ X11 @ X10)
% 6.79/7.01          | ~ (v1_relat_1 @ X11))),
% 6.79/7.01      inference('cnf', [status(esa)], [d3_relat_1])).
% 6.79/7.01  thf(t117_relat_1, axiom,
% 6.79/7.01    (![A:$i,B:$i]:
% 6.79/7.01     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 6.79/7.01  thf('15', plain,
% 6.79/7.01      (![X17 : $i, X18 : $i]:
% 6.79/7.01         ((r1_tarski @ (k8_relat_1 @ X17 @ X18) @ X18) | ~ (v1_relat_1 @ X18))),
% 6.79/7.01      inference('cnf', [status(esa)], [t117_relat_1])).
% 6.79/7.01  thf('16', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (r2_hidden @ X0 @ X1)
% 6.79/7.01          | (r2_hidden @ X0 @ X2)
% 6.79/7.01          | ~ (r1_tarski @ X1 @ X2))),
% 6.79/7.01      inference('cnf', [status(esa)], [d3_tarski])).
% 6.79/7.01  thf('17', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X0)
% 6.79/7.01          | (r2_hidden @ X2 @ X0)
% 6.79/7.01          | ~ (r2_hidden @ X2 @ (k8_relat_1 @ X1 @ X0)))),
% 6.79/7.01      inference('sup-', [status(thm)], ['15', '16'])).
% 6.79/7.01  thf('18', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 6.79/7.01              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 6.79/7.01             X0)
% 6.79/7.01          | ~ (v1_relat_1 @ X0))),
% 6.79/7.01      inference('sup-', [status(thm)], ['14', '17'])).
% 6.79/7.01  thf('19', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X0)
% 6.79/7.01          | ~ (v1_relat_1 @ X0)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 6.79/7.01              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 6.79/7.01             X0)
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2))),
% 6.79/7.01      inference('sup-', [status(thm)], ['13', '18'])).
% 6.79/7.01  thf('20', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 6.79/7.01              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 6.79/7.01             X0)
% 6.79/7.01          | ~ (v1_relat_1 @ X0))),
% 6.79/7.01      inference('simplify', [status(thm)], ['19'])).
% 6.79/7.01  thf('21', plain, ((r1_tarski @ sk_C_2 @ sk_D_2)),
% 6.79/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.01  thf('22', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         (~ (r2_hidden @ X0 @ X1)
% 6.79/7.01          | (r2_hidden @ X0 @ X2)
% 6.79/7.01          | ~ (r1_tarski @ X1 @ X2))),
% 6.79/7.01      inference('cnf', [status(esa)], [d3_tarski])).
% 6.79/7.01  thf('23', plain,
% 6.79/7.01      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_2) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 6.79/7.01      inference('sup-', [status(thm)], ['21', '22'])).
% 6.79/7.01  thf('24', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ sk_C_2)
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_2) @ X1)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2)) @ 
% 6.79/7.01              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2))) @ 
% 6.79/7.01             sk_D_2))),
% 6.79/7.01      inference('sup-', [status(thm)], ['20', '23'])).
% 6.79/7.01  thf('25', plain, ((v1_relat_1 @ sk_C_2)),
% 6.79/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.01  thf('26', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i]:
% 6.79/7.01         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_2) @ X1)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2)) @ 
% 6.79/7.01              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2))) @ 
% 6.79/7.01             sk_D_2))),
% 6.79/7.01      inference('demod', [status(thm)], ['24', '25'])).
% 6.79/7.01  thf('27', plain,
% 6.79/7.01      (![X15 : $i, X16 : $i]:
% 6.79/7.01         ((v1_relat_1 @ (k8_relat_1 @ X15 @ X16)) | ~ (v1_relat_1 @ X16))),
% 6.79/7.01      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 6.79/7.01  thf('28', plain,
% 6.79/7.01      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X4)
% 6.79/7.01          | ((X4) != (k8_relat_1 @ X5 @ X6))
% 6.79/7.01          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ X4)
% 6.79/7.01          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X6)
% 6.79/7.01          | ~ (r2_hidden @ X8 @ X5)
% 6.79/7.01          | ~ (v1_relat_1 @ X6))),
% 6.79/7.01      inference('cnf', [status(esa)], [d12_relat_1])).
% 6.79/7.01  thf('29', plain,
% 6.79/7.01      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X6)
% 6.79/7.01          | ~ (r2_hidden @ X8 @ X5)
% 6.79/7.01          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X6)
% 6.79/7.01          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k8_relat_1 @ X5 @ X6))
% 6.79/7.01          | ~ (v1_relat_1 @ (k8_relat_1 @ X5 @ X6)))),
% 6.79/7.01      inference('simplify', [status(thm)], ['28'])).
% 6.79/7.01  thf('30', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.79/7.01         (~ (v1_relat_1 @ X0)
% 6.79/7.01          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 6.79/7.01          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 6.79/7.01          | ~ (r2_hidden @ X2 @ X1)
% 6.79/7.01          | ~ (v1_relat_1 @ X0))),
% 6.79/7.01      inference('sup-', [status(thm)], ['27', '29'])).
% 6.79/7.01  thf('31', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.79/7.01         (~ (r2_hidden @ X2 @ X1)
% 6.79/7.01          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 6.79/7.01          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 6.79/7.01          | ~ (v1_relat_1 @ X0))),
% 6.79/7.01      inference('simplify', [status(thm)], ['30'])).
% 6.79/7.01  thf('32', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_2) @ X1)
% 6.79/7.01          | ~ (v1_relat_1 @ sk_D_2)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2)) @ 
% 6.79/7.01              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2))) @ 
% 6.79/7.01             (k8_relat_1 @ X2 @ sk_D_2))
% 6.79/7.01          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2)) @ X2))),
% 6.79/7.01      inference('sup-', [status(thm)], ['26', '31'])).
% 6.79/7.01  thf('33', plain, ((v1_relat_1 @ sk_D_2)),
% 6.79/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.01  thf('34', plain,
% 6.79/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.01         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_2) @ X1)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2)) @ 
% 6.79/7.01              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2))) @ 
% 6.79/7.01             (k8_relat_1 @ X2 @ sk_D_2))
% 6.79/7.01          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_2)) @ X2))),
% 6.79/7.01      inference('demod', [status(thm)], ['32', '33'])).
% 6.79/7.01  thf('35', plain,
% 6.79/7.01      (![X0 : $i]:
% 6.79/7.01         ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ X0)
% 6.79/7.01          | ~ (v1_relat_1 @ sk_C_2)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_2)) @ 
% 6.79/7.01              (sk_D_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_2))) @ 
% 6.79/7.01             (k8_relat_1 @ sk_B @ sk_D_2))
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ X0))),
% 6.79/7.01      inference('sup-', [status(thm)], ['12', '34'])).
% 6.79/7.01  thf('36', plain, ((v1_relat_1 @ sk_C_2)),
% 6.79/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.01  thf('37', plain,
% 6.79/7.01      (![X0 : $i]:
% 6.79/7.01         ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ X0)
% 6.79/7.01          | (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_2)) @ 
% 6.79/7.01              (sk_D_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_2))) @ 
% 6.79/7.01             (k8_relat_1 @ sk_B @ sk_D_2))
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ X0))),
% 6.79/7.01      inference('demod', [status(thm)], ['35', '36'])).
% 6.79/7.01  thf('38', plain,
% 6.79/7.01      (![X0 : $i]:
% 6.79/7.01         ((r2_hidden @ 
% 6.79/7.01           (k4_tarski @ (sk_C_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_2)) @ 
% 6.79/7.01            (sk_D_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_2))) @ 
% 6.79/7.01           (k8_relat_1 @ sk_B @ sk_D_2))
% 6.79/7.01          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ X0))),
% 6.79/7.01      inference('simplify', [status(thm)], ['37'])).
% 6.79/7.01  thf('39', plain,
% 6.79/7.01      (![X10 : $i, X11 : $i]:
% 6.79/7.01         (~ (r2_hidden @ 
% 6.79/7.01             (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X10)
% 6.79/7.01          | (r1_tarski @ X11 @ X10)
% 6.79/7.01          | ~ (v1_relat_1 @ X11))),
% 6.79/7.01      inference('cnf', [status(esa)], [d3_relat_1])).
% 6.79/7.01  thf('40', plain,
% 6.79/7.01      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ 
% 6.79/7.01         (k8_relat_1 @ sk_B @ sk_D_2))
% 6.79/7.01        | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_2))
% 6.79/7.01        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ 
% 6.79/7.01           (k8_relat_1 @ sk_B @ sk_D_2)))),
% 6.79/7.01      inference('sup-', [status(thm)], ['38', '39'])).
% 6.79/7.01  thf('41', plain,
% 6.79/7.01      ((~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_2))
% 6.79/7.01        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ 
% 6.79/7.01           (k8_relat_1 @ sk_B @ sk_D_2)))),
% 6.79/7.01      inference('simplify', [status(thm)], ['40'])).
% 6.79/7.01  thf('42', plain,
% 6.79/7.01      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_2) @ 
% 6.79/7.01          (k8_relat_1 @ sk_B @ sk_D_2))),
% 6.79/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.01  thf('43', plain, (~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_2))),
% 6.79/7.01      inference('clc', [status(thm)], ['41', '42'])).
% 6.79/7.01  thf('44', plain, (~ (v1_relat_1 @ sk_C_2)),
% 6.79/7.01      inference('sup-', [status(thm)], ['0', '43'])).
% 6.79/7.01  thf('45', plain, ((v1_relat_1 @ sk_C_2)),
% 6.79/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.01  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 6.79/7.01  
% 6.79/7.01  % SZS output end Refutation
% 6.79/7.01  
% 6.79/7.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
