%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Qrz2i4EMk

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:45 EST 2020

% Result     : Theorem 14.45s
% Output     : Refutation 14.45s
% Verified   : 
% Statistics : Number of formulae       :   71 (  93 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   20
%              Number of atoms          :  902 (1234 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

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

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t131_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k8_relat_1 @ X13 @ X15 ) @ ( k8_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t131_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D_1 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) ) @ ( k8_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ X1 @ sk_C_1 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ X1 @ sk_C_1 ) ) ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ X1 @ sk_C_1 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ X1 @ sk_C_1 ) ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ ( k8_relat_1 @ X2 @ sk_D_2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ ( k8_relat_1 @ X2 @ sk_D_2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('47',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Qrz2i4EMk
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 14.45/14.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 14.45/14.67  % Solved by: fo/fo7.sh
% 14.45/14.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.45/14.67  % done 4701 iterations in 14.219s
% 14.45/14.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 14.45/14.67  % SZS output start Refutation
% 14.45/14.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.45/14.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.45/14.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 14.45/14.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.45/14.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 14.45/14.67  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 14.45/14.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 14.45/14.67  thf(sk_A_type, type, sk_A: $i).
% 14.45/14.67  thf(sk_D_2_type, type, sk_D_2: $i).
% 14.45/14.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 14.45/14.67  thf(sk_B_type, type, sk_B: $i).
% 14.45/14.67  thf(dt_k8_relat_1, axiom,
% 14.45/14.67    (![A:$i,B:$i]:
% 14.45/14.67     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 14.45/14.67  thf('0', plain,
% 14.45/14.67      (![X11 : $i, X12 : $i]:
% 14.45/14.67         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 14.45/14.67      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 14.45/14.67  thf('1', plain,
% 14.45/14.67      (![X11 : $i, X12 : $i]:
% 14.45/14.67         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 14.45/14.67      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 14.45/14.67  thf('2', plain,
% 14.45/14.67      (![X11 : $i, X12 : $i]:
% 14.45/14.67         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 14.45/14.67      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 14.45/14.67  thf(t133_relat_1, conjecture,
% 14.45/14.67    (![A:$i,B:$i,C:$i]:
% 14.45/14.67     ( ( v1_relat_1 @ C ) =>
% 14.45/14.67       ( ![D:$i]:
% 14.45/14.67         ( ( v1_relat_1 @ D ) =>
% 14.45/14.67           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 14.45/14.67             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 14.45/14.67  thf(zf_stmt_0, negated_conjecture,
% 14.45/14.67    (~( ![A:$i,B:$i,C:$i]:
% 14.45/14.67        ( ( v1_relat_1 @ C ) =>
% 14.45/14.67          ( ![D:$i]:
% 14.45/14.67            ( ( v1_relat_1 @ D ) =>
% 14.45/14.67              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 14.45/14.67                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 14.45/14.67    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 14.45/14.67  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 14.45/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.45/14.67  thf(t131_relat_1, axiom,
% 14.45/14.67    (![A:$i,B:$i,C:$i]:
% 14.45/14.67     ( ( v1_relat_1 @ C ) =>
% 14.45/14.67       ( ( r1_tarski @ A @ B ) =>
% 14.45/14.67         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 14.45/14.67  thf('4', plain,
% 14.45/14.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.45/14.67         (~ (r1_tarski @ X13 @ X14)
% 14.45/14.67          | ~ (v1_relat_1 @ X15)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X13 @ X15) @ (k8_relat_1 @ X14 @ X15)))),
% 14.45/14.67      inference('cnf', [status(esa)], [t131_relat_1])).
% 14.45/14.67  thf('5', plain,
% 14.45/14.67      (![X0 : $i]:
% 14.45/14.67         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0))
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('sup-', [status(thm)], ['3', '4'])).
% 14.45/14.67  thf(d3_relat_1, axiom,
% 14.45/14.67    (![A:$i]:
% 14.45/14.67     ( ( v1_relat_1 @ A ) =>
% 14.45/14.67       ( ![B:$i]:
% 14.45/14.67         ( ( r1_tarski @ A @ B ) <=>
% 14.45/14.67           ( ![C:$i,D:$i]:
% 14.45/14.67             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 14.45/14.67               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 14.45/14.67  thf('6', plain,
% 14.45/14.67      (![X6 : $i, X7 : $i]:
% 14.45/14.67         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 14.45/14.67          | (r1_tarski @ X7 @ X6)
% 14.45/14.67          | ~ (v1_relat_1 @ X7))),
% 14.45/14.67      inference('cnf', [status(esa)], [d3_relat_1])).
% 14.45/14.67  thf('7', plain,
% 14.45/14.67      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 14.45/14.67         (~ (r1_tarski @ X7 @ X8)
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ X8)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X7)
% 14.45/14.67          | ~ (v1_relat_1 @ X7))),
% 14.45/14.67      inference('cnf', [status(esa)], [d3_relat_1])).
% 14.45/14.67  thf('8', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r1_tarski @ X0 @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D_1 @ X1 @ X0)) @ 
% 14.45/14.67             X2)
% 14.45/14.67          | ~ (r1_tarski @ X0 @ X2))),
% 14.45/14.67      inference('sup-', [status(thm)], ['6', '7'])).
% 14.45/14.67  thf('9', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         (~ (r1_tarski @ X0 @ X2)
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D_1 @ X1 @ X0)) @ 
% 14.45/14.67             X2)
% 14.45/14.67          | (r1_tarski @ X0 @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['8'])).
% 14.45/14.67  thf('10', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0))) @ 
% 14.45/14.67             (k8_relat_1 @ sk_B @ X0)))),
% 14.45/14.67      inference('sup-', [status(thm)], ['5', '9'])).
% 14.45/14.67  thf('11', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0))) @ 
% 14.45/14.67             (k8_relat_1 @ sk_B @ X0))
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('sup-', [status(thm)], ['2', '10'])).
% 14.45/14.67  thf('12', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0))) @ 
% 14.45/14.67             (k8_relat_1 @ sk_B @ X0))
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['11'])).
% 14.45/14.67  thf(d12_relat_1, axiom,
% 14.45/14.67    (![A:$i,B:$i]:
% 14.45/14.67     ( ( v1_relat_1 @ B ) =>
% 14.45/14.67       ( ![C:$i]:
% 14.45/14.67         ( ( v1_relat_1 @ C ) =>
% 14.45/14.67           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 14.45/14.67             ( ![D:$i,E:$i]:
% 14.45/14.67               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 14.45/14.67                 ( ( r2_hidden @ E @ A ) & 
% 14.45/14.67                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 14.45/14.67  thf('13', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 14.45/14.67          | (r2_hidden @ X5 @ X1)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 14.45/14.67          | ~ (v1_relat_1 @ X2))),
% 14.45/14.67      inference('cnf', [status(esa)], [d12_relat_1])).
% 14.45/14.67  thf('14', plain,
% 14.45/14.67      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X2)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 14.45/14.67          | (r2_hidden @ X5 @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 14.45/14.67      inference('simplify', [status(thm)], ['13'])).
% 14.45/14.67  thf('15', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ X0))
% 14.45/14.67          | (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('sup-', [status(thm)], ['12', '14'])).
% 14.45/14.67  thf('16', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         ((r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B)
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ X0))
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['15'])).
% 14.45/14.67  thf('17', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | ~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 14.45/14.67          | (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B))),
% 14.45/14.67      inference('sup-', [status(thm)], ['1', '16'])).
% 14.45/14.67  thf('18', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         ((r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['17'])).
% 14.45/14.67  thf('19', plain, ((r1_tarski @ sk_C_1 @ sk_D_2)),
% 14.45/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.45/14.67  thf('20', plain,
% 14.45/14.67      (![X11 : $i, X12 : $i]:
% 14.45/14.67         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 14.45/14.67      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 14.45/14.67  thf('21', plain,
% 14.45/14.67      (![X6 : $i, X7 : $i]:
% 14.45/14.67         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 14.45/14.67          | (r1_tarski @ X7 @ X6)
% 14.45/14.67          | ~ (v1_relat_1 @ X7))),
% 14.45/14.67      inference('cnf', [status(esa)], [d3_relat_1])).
% 14.45/14.67  thf('22', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 14.45/14.67          | ~ (v1_relat_1 @ X2))),
% 14.45/14.67      inference('cnf', [status(esa)], [d12_relat_1])).
% 14.45/14.67  thf('23', plain,
% 14.45/14.67      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X2)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 14.45/14.67      inference('simplify', [status(thm)], ['22'])).
% 14.45/14.67  thf('24', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 14.45/14.67             X0)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('sup-', [status(thm)], ['21', '23'])).
% 14.45/14.67  thf('25', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 14.45/14.67             X0)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 14.45/14.67      inference('simplify', [status(thm)], ['24'])).
% 14.45/14.67  thf('26', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 14.45/14.67             X0)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('sup-', [status(thm)], ['20', '25'])).
% 14.45/14.67  thf('27', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         ((r2_hidden @ 
% 14.45/14.67           (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 14.45/14.67            (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 14.45/14.67           X0)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['26'])).
% 14.45/14.67  thf('28', plain,
% 14.45/14.67      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 14.45/14.67         (~ (r1_tarski @ X7 @ X8)
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ X8)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X7)
% 14.45/14.67          | ~ (v1_relat_1 @ X7))),
% 14.45/14.67      inference('cnf', [status(esa)], [d3_relat_1])).
% 14.45/14.67  thf('29', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 14.45/14.67          | ~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 14.45/14.67             X3)
% 14.45/14.67          | ~ (r1_tarski @ X0 @ X3))),
% 14.45/14.67      inference('sup-', [status(thm)], ['27', '28'])).
% 14.45/14.67  thf('30', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.45/14.67         (~ (r1_tarski @ X0 @ X3)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 14.45/14.67              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 14.45/14.67             X3)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['29'])).
% 14.45/14.67  thf('31', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ sk_C_1)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ X1 @ sk_C_1) @ X0)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ X1 @ sk_C_1)) @ 
% 14.45/14.67              (sk_D_1 @ X0 @ (k8_relat_1 @ X1 @ sk_C_1))) @ 
% 14.45/14.67             sk_D_2))),
% 14.45/14.67      inference('sup-', [status(thm)], ['19', '30'])).
% 14.45/14.67  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 14.45/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.45/14.67  thf('33', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i]:
% 14.45/14.67         ((r1_tarski @ (k8_relat_1 @ X1 @ sk_C_1) @ X0)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ X1 @ sk_C_1)) @ 
% 14.45/14.67              (sk_D_1 @ X0 @ (k8_relat_1 @ X1 @ sk_C_1))) @ 
% 14.45/14.67             sk_D_2))),
% 14.45/14.67      inference('demod', [status(thm)], ['31', '32'])).
% 14.45/14.67  thf('34', plain,
% 14.45/14.67      (![X11 : $i, X12 : $i]:
% 14.45/14.67         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 14.45/14.67      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 14.45/14.67  thf('35', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 14.45/14.67          | ~ (r2_hidden @ X4 @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ X2))),
% 14.45/14.67      inference('cnf', [status(esa)], [d12_relat_1])).
% 14.45/14.67  thf('36', plain,
% 14.45/14.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X2)
% 14.45/14.67          | ~ (r2_hidden @ X4 @ X1)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k8_relat_1 @ X1 @ X2))
% 14.45/14.67          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 14.45/14.67      inference('simplify', [status(thm)], ['35'])).
% 14.45/14.67  thf('37', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ X0)
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 14.45/14.67          | ~ (r2_hidden @ X2 @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('sup-', [status(thm)], ['34', '36'])).
% 14.45/14.67  thf('38', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.45/14.67         (~ (r2_hidden @ X2 @ X1)
% 14.45/14.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 14.45/14.67          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 14.45/14.67          | ~ (v1_relat_1 @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['37'])).
% 14.45/14.67  thf('39', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1)
% 14.45/14.67          | ~ (v1_relat_1 @ sk_D_2)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 14.45/14.67              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 14.45/14.67             (k8_relat_1 @ X2 @ sk_D_2))
% 14.45/14.67          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ X2))),
% 14.45/14.67      inference('sup-', [status(thm)], ['33', '38'])).
% 14.45/14.67  thf('40', plain, ((v1_relat_1 @ sk_D_2)),
% 14.45/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.45/14.67  thf('41', plain,
% 14.45/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.45/14.67         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 14.45/14.67              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 14.45/14.67             (k8_relat_1 @ X2 @ sk_D_2))
% 14.45/14.67          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ X2))),
% 14.45/14.67      inference('demod', [status(thm)], ['39', '40'])).
% 14.45/14.67  thf('42', plain,
% 14.45/14.67      (![X0 : $i]:
% 14.45/14.67         (~ (v1_relat_1 @ sk_C_1)
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1)) @ 
% 14.45/14.67              (sk_D_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1))) @ 
% 14.45/14.67             (k8_relat_1 @ sk_B @ sk_D_2))
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0))),
% 14.45/14.67      inference('sup-', [status(thm)], ['18', '41'])).
% 14.45/14.67  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 14.45/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.45/14.67  thf('44', plain,
% 14.45/14.67      (![X0 : $i]:
% 14.45/14.67         ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0)
% 14.45/14.67          | (r2_hidden @ 
% 14.45/14.67             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1)) @ 
% 14.45/14.67              (sk_D_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1))) @ 
% 14.45/14.67             (k8_relat_1 @ sk_B @ sk_D_2))
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0))),
% 14.45/14.67      inference('demod', [status(thm)], ['42', '43'])).
% 14.45/14.67  thf('45', plain,
% 14.45/14.67      (![X0 : $i]:
% 14.45/14.67         ((r2_hidden @ 
% 14.45/14.67           (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1)) @ 
% 14.45/14.67            (sk_D_1 @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1))) @ 
% 14.45/14.67           (k8_relat_1 @ sk_B @ sk_D_2))
% 14.45/14.67          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0))),
% 14.45/14.67      inference('simplify', [status(thm)], ['44'])).
% 14.45/14.67  thf('46', plain,
% 14.45/14.67      (![X6 : $i, X7 : $i]:
% 14.45/14.67         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ 
% 14.45/14.67             X6)
% 14.45/14.67          | (r1_tarski @ X7 @ X6)
% 14.45/14.67          | ~ (v1_relat_1 @ X7))),
% 14.45/14.67      inference('cnf', [status(esa)], [d3_relat_1])).
% 14.45/14.67  thf('47', plain,
% 14.45/14.67      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 14.45/14.67         (k8_relat_1 @ sk_B @ sk_D_2))
% 14.45/14.67        | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1))
% 14.45/14.67        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 14.45/14.67           (k8_relat_1 @ sk_B @ sk_D_2)))),
% 14.45/14.67      inference('sup-', [status(thm)], ['45', '46'])).
% 14.45/14.67  thf('48', plain,
% 14.45/14.67      ((~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1))
% 14.45/14.67        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 14.45/14.67           (k8_relat_1 @ sk_B @ sk_D_2)))),
% 14.45/14.67      inference('simplify', [status(thm)], ['47'])).
% 14.45/14.67  thf('49', plain,
% 14.45/14.67      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 14.45/14.67          (k8_relat_1 @ sk_B @ sk_D_2))),
% 14.45/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.45/14.67  thf('50', plain, (~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1))),
% 14.45/14.67      inference('clc', [status(thm)], ['48', '49'])).
% 14.45/14.67  thf('51', plain, (~ (v1_relat_1 @ sk_C_1)),
% 14.45/14.67      inference('sup-', [status(thm)], ['0', '50'])).
% 14.45/14.67  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 14.45/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.45/14.67  thf('53', plain, ($false), inference('demod', [status(thm)], ['51', '52'])).
% 14.45/14.67  
% 14.45/14.67  % SZS output end Refutation
% 14.45/14.67  
% 14.45/14.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
