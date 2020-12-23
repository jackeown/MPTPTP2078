%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nWdiBSChlH

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  415 ( 590 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t179_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t179_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) @ X2 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) @ X2 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).


%------------------------------------------------------------------------------
