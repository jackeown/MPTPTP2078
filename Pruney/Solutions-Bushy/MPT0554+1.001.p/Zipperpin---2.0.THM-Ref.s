%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0554+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qlpyFEfS8R

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:05 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  375 ( 486 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   18 (   8 average)

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

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t156_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_relat_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
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
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X5 ) @ X2 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X5 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23'])).


%------------------------------------------------------------------------------
