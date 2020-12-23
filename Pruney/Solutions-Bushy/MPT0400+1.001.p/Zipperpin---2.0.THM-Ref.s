%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0400+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MnPlVnKGyO

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  327 ( 543 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t23_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_setfam_1 @ A @ B )
        & ( r1_setfam_1 @ B @ C ) )
     => ( r1_setfam_1 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_setfam_1 @ A @ B )
          & ( r1_setfam_1 @ B @ C ) )
       => ( r1_setfam_1 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t23_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('2',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_setfam_1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_setfam_1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ~ ( r1_setfam_1 @ sk_B @ X1 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r1_tarski @ ( sk_C @ X3 @ X2 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) @ X0 )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_B ) @ sk_C_1 ) @ X0 )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_C_1 )
    | ( r1_setfam_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    r1_setfam_1 @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).


%------------------------------------------------------------------------------
