%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oayyYjmCds

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :   20
%              Number of atoms          :  743 ( 990 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t132_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_B ) @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

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

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ X1 @ sk_B ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ X1 @ sk_B ) ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ X1 @ sk_B ) ) @ ( sk_D_1 @ X0 @ ( k8_relat_1 @ X1 @ sk_B ) ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) @ ( k8_relat_1 @ X2 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) @ ( k8_relat_1 @ X2 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( sk_D_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oayyYjmCds
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:14:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 100 iterations in 0.096s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.56  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(t132_relat_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( v1_relat_1 @ B ) =>
% 0.22/0.56       ( ![C:$i]:
% 0.22/0.56         ( ( v1_relat_1 @ C ) =>
% 0.22/0.56           ( ( r1_tarski @ B @ C ) =>
% 0.22/0.56             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i]:
% 0.22/0.56        ( ( v1_relat_1 @ B ) =>
% 0.22/0.56          ( ![C:$i]:
% 0.22/0.56            ( ( v1_relat_1 @ C ) =>
% 0.22/0.56              ( ( r1_tarski @ B @ C ) =>
% 0.22/0.56                ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t132_relat_1])).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_B) @ (k8_relat_1 @ sk_A @ sk_C_1))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_k8_relat_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.22/0.56  thf(d3_relat_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( v1_relat_1 @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.56           ( ![C:$i,D:$i]:
% 0.22/0.56             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.22/0.56               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (![X6 : $i, X7 : $i]:
% 0.22/0.56         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 0.22/0.56          | (r1_tarski @ X7 @ X6)
% 0.22/0.56          | ~ (v1_relat_1 @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.56  thf(d12_relat_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( v1_relat_1 @ B ) =>
% 0.22/0.56       ( ![C:$i]:
% 0.22/0.56         ( ( v1_relat_1 @ C ) =>
% 0.22/0.56           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.22/0.56             ( ![D:$i,E:$i]:
% 0.22/0.56               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.22/0.56                 ( ( r2_hidden @ E @ A ) & 
% 0.22/0.56                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.22/0.56          | (r2_hidden @ X5 @ X1)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.22/0.56          | ~ (v1_relat_1 @ X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X2)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.22/0.56          | (r2_hidden @ X5 @ X1)
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.56          | (r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['3', '5'])).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | (r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((r2_hidden @ (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.56  thf('10', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X6 : $i, X7 : $i]:
% 0.22/0.56         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 0.22/0.56          | (r1_tarski @ X7 @ X6)
% 0.22/0.56          | ~ (v1_relat_1 @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.22/0.56          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.22/0.56          | ~ (v1_relat_1 @ X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X2)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.22/0.56          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.22/0.56              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.22/0.56             X0)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.22/0.56              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.22/0.56             X0)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.22/0.56              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.22/0.56             X0)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '16'])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((r2_hidden @ 
% 0.22/0.56           (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.22/0.56            (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.22/0.56           X0)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X7 @ X8)
% 0.22/0.56          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ X8)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X7)
% 0.22/0.56          | ~ (v1_relat_1 @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ X0)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.22/0.56              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.22/0.56             X3)
% 0.22/0.56          | ~ (r1_tarski @ X0 @ X3))),
% 0.22/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X0 @ X3)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.22/0.56              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.22/0.56             X3)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ sk_B)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X1 @ sk_B) @ X0)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ X1 @ sk_B)) @ 
% 0.22/0.56              (sk_D_1 @ X0 @ (k8_relat_1 @ X1 @ sk_B))) @ 
% 0.22/0.56             sk_C_1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['10', '21'])).
% 0.22/0.56  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((r1_tarski @ (k8_relat_1 @ X1 @ sk_B) @ X0)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ X1 @ sk_B)) @ 
% 0.22/0.56              (sk_D_1 @ X0 @ (k8_relat_1 @ X1 @ sk_B))) @ 
% 0.22/0.56             sk_C_1))),
% 0.22/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.22/0.56          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X4 @ X1)
% 0.22/0.56          | ~ (v1_relat_1 @ X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X4 @ X1)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.22/0.56          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k8_relat_1 @ X1 @ X2))
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 0.22/0.56          | ~ (r2_hidden @ X2 @ X1)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['25', '27'])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X2 @ X1)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 0.22/0.56          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ X1)
% 0.22/0.56          | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 0.22/0.56              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B))) @ 
% 0.22/0.56             (k8_relat_1 @ X2 @ sk_C_1))
% 0.22/0.56          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B)) @ X2))),
% 0.22/0.56      inference('sup-', [status(thm)], ['24', '29'])).
% 0.22/0.56  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ X1)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 0.22/0.56              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B))) @ 
% 0.22/0.56             (k8_relat_1 @ X2 @ sk_C_1))
% 0.22/0.56          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B)) @ X2))),
% 0.22/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ sk_B)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ X1)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 0.22/0.56              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B))) @ 
% 0.22/0.56             (k8_relat_1 @ X0 @ sk_C_1))
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ X1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['9', '32'])).
% 0.22/0.56  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ X1)
% 0.22/0.56          | (r2_hidden @ 
% 0.22/0.56             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 0.22/0.56              (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B))) @ 
% 0.22/0.56             (k8_relat_1 @ X0 @ sk_C_1))
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ X1))),
% 0.22/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((r2_hidden @ 
% 0.22/0.56           (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 0.22/0.56            (sk_D_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B))) @ 
% 0.22/0.56           (k8_relat_1 @ X0 @ sk_C_1))
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ X1))),
% 0.22/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      (![X6 : $i, X7 : $i]:
% 0.22/0.56         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ 
% 0.22/0.56             X6)
% 0.22/0.56          | (r1_tarski @ X7 @ X6)
% 0.22/0.56          | ~ (v1_relat_1 @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ (k8_relat_1 @ X0 @ sk_C_1))
% 0.22/0.56          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ (k8_relat_1 @ X0 @ sk_C_1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ (k8_relat_1 @ X0 @ sk_C_1)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ sk_B)
% 0.22/0.56          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ (k8_relat_1 @ X0 @ sk_C_1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['1', '39'])).
% 0.22/0.56  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ (k8_relat_1 @ X0 @ sk_C_1))),
% 0.22/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.56  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
