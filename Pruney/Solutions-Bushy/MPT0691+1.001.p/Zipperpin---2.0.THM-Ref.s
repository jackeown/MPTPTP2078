%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0691+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TMRZd8ikJ3

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:20 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  414 ( 637 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( sk_D_3 @ X24 @ X22 ) ) @ X22 )
      | ( X23
       != ( k1_relat_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X24 @ ( sk_D_3 @ X24 @ X22 ) ) @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

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

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

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

thf('18',plain,(
    ! [X9: $i,X10: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X12
       != ( k10_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X10 )
      | ~ ( r2_hidden @ X15 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( r2_hidden @ X15 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X10 )
      | ( r2_hidden @ X14 @ ( k10_relat_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X19 )
      | ~ ( r2_hidden @ ( sk_C @ X19 @ X17 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).


%------------------------------------------------------------------------------
