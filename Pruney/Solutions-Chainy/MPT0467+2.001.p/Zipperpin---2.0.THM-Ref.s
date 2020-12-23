%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pAxRK2JRav

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:14 EST 2020

% Result     : Theorem 10.21s
% Output     : Refutation 10.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 474 expanded)
%              Number of leaves         :   18 ( 123 expanded)
%              Depth                    :   48
%              Number of atoms          : 5537 (14066 expanded)
%              Number of equality atoms :   76 ( 209 expanded)
%              Maximal formula depth    :   31 (  15 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('13',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['23','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 @ X1 ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F_1 @ ( sk_F_1 @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X1 @ X2 ) ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) ) @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( sk_D @ X3 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('65',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_F @ X13 @ X11 @ X12 ) ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('71',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) ) @ ( k5_relat_1 @ X4 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) ) @ ( k5_relat_1 @ X4 @ X0 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('84',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('85',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) ) @ ( k5_relat_1 @ X4 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) @ X0 @ X2 ) ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F_1 @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) @ ( sk_F @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) @ X0 @ X2 ) ) @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) ) @ ( k5_relat_1 @ X4 @ X0 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['66','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ X3 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ~ ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X3 )
      | ~ ( r1_tarski @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('118',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('120',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('128',plain,(
    ! [X11: $i,X12: $i,X13: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ X18 ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_D_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf(t55_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                  = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_relat_1])).

thf('141',plain,(
    ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C_1 ) )
     != ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C_1 ) )
 != ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    $false ),
    inference(simplify,[status(thm)],['146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pAxRK2JRav
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.21/10.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.21/10.42  % Solved by: fo/fo7.sh
% 10.21/10.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.21/10.42  % done 1537 iterations in 9.965s
% 10.21/10.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.21/10.42  % SZS output start Refutation
% 10.21/10.42  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 10.21/10.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.21/10.42  thf(sk_C_1_type, type, sk_C_1: $i).
% 10.21/10.42  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 10.21/10.42  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 10.21/10.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.21/10.42  thf(sk_B_type, type, sk_B: $i).
% 10.21/10.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.21/10.42  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.21/10.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.21/10.42  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 10.21/10.42  thf(sk_A_type, type, sk_A: $i).
% 10.21/10.42  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 10.21/10.42  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 10.21/10.42  thf(dt_k5_relat_1, axiom,
% 10.21/10.42    (![A:$i,B:$i]:
% 10.21/10.42     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 10.21/10.43       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 10.21/10.43  thf('0', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('1', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('2', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('3', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('4', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('5', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('6', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('7', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('8', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('9', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('10', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf(d3_relat_1, axiom,
% 10.21/10.43    (![A:$i]:
% 10.21/10.43     ( ( v1_relat_1 @ A ) =>
% 10.21/10.43       ( ![B:$i]:
% 10.21/10.43         ( ( r1_tarski @ A @ B ) <=>
% 10.21/10.43           ( ![C:$i,D:$i]:
% 10.21/10.43             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 10.21/10.43               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 10.21/10.43  thf('11', plain,
% 10.21/10.43      (![X6 : $i, X7 : $i]:
% 10.21/10.43         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D @ X6 @ X7)) @ X7)
% 10.21/10.43          | (r1_tarski @ X7 @ X6)
% 10.21/10.43          | ~ (v1_relat_1 @ X7))),
% 10.21/10.43      inference('cnf', [status(esa)], [d3_relat_1])).
% 10.21/10.43  thf(d8_relat_1, axiom,
% 10.21/10.43    (![A:$i]:
% 10.21/10.43     ( ( v1_relat_1 @ A ) =>
% 10.21/10.43       ( ![B:$i]:
% 10.21/10.43         ( ( v1_relat_1 @ B ) =>
% 10.21/10.43           ( ![C:$i]:
% 10.21/10.43             ( ( v1_relat_1 @ C ) =>
% 10.21/10.43               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 10.21/10.43                 ( ![D:$i,E:$i]:
% 10.21/10.43                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 10.21/10.43                     ( ?[F:$i]:
% 10.21/10.43                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 10.21/10.43                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 10.21/10.43  thf('12', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X11)
% 10.21/10.43          | ((X13) != (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X14 @ (sk_F_1 @ X17 @ X14 @ X11 @ X12)) @ X12)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X12))),
% 10.21/10.43      inference('cnf', [status(esa)], [d8_relat_1])).
% 10.21/10.43  thf('13', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X14 @ (sk_F_1 @ X17 @ X14 @ X11 @ X12)) @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['12'])).
% 10.21/10.43  thf('14', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['11', '13'])).
% 10.21/10.43  thf('15', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('simplify', [status(thm)], ['14'])).
% 10.21/10.43  thf('16', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['10', '15'])).
% 10.21/10.43  thf('17', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43            (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43             (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 10.21/10.43           X1)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['16'])).
% 10.21/10.43  thf('18', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X14 @ (sk_F_1 @ X17 @ X14 @ X11 @ X12)) @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['12'])).
% 10.21/10.43  thf('19', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['17', '18'])).
% 10.21/10.43  thf('20', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X2))),
% 10.21/10.43      inference('simplify', [status(thm)], ['19'])).
% 10.21/10.43  thf('21', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['9', '20'])).
% 10.21/10.43  thf('22', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_F_1 @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43             (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ X1)) @ 
% 10.21/10.43           X1)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['21'])).
% 10.21/10.43  thf('23', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('24', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('25', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43            (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43             (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 10.21/10.43           X1)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['16'])).
% 10.21/10.43  thf('26', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X11)
% 10.21/10.43          | ((X13) != (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X12))),
% 10.21/10.43      inference('cnf', [status(esa)], [d8_relat_1])).
% 10.21/10.43  thf('27', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['26'])).
% 10.21/10.43  thf('28', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['25', '27'])).
% 10.21/10.43  thf('29', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X2))),
% 10.21/10.43      inference('simplify', [status(thm)], ['28'])).
% 10.21/10.43  thf('30', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['24', '29'])).
% 10.21/10.43  thf('31', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_F_1 @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43             (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ X1) @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43           X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['30'])).
% 10.21/10.43  thf('32', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('33', plain,
% 10.21/10.43      (![X6 : $i, X7 : $i]:
% 10.21/10.43         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D @ X6 @ X7)) @ X7)
% 10.21/10.43          | (r1_tarski @ X7 @ X6)
% 10.21/10.43          | ~ (v1_relat_1 @ X7))),
% 10.21/10.43      inference('cnf', [status(esa)], [d3_relat_1])).
% 10.21/10.43  thf('34', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['26'])).
% 10.21/10.43  thf('35', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 10.21/10.43              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['33', '34'])).
% 10.21/10.43  thf('36', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 10.21/10.43              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('simplify', [status(thm)], ['35'])).
% 10.21/10.43  thf('37', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 10.21/10.43              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['32', '36'])).
% 10.21/10.43  thf('38', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43             (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 10.21/10.43            (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43           X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['37'])).
% 10.21/10.43  thf('39', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('40', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X11)
% 10.21/10.43          | ((X13) != (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X16 @ X15) @ X11)
% 10.21/10.43          | ~ (v1_relat_1 @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X12))),
% 10.21/10.43      inference('cnf', [status(esa)], [d8_relat_1])).
% 10.21/10.43  thf('41', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X16 @ X15) @ X11)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['40'])).
% 10.21/10.43  thf('42', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['39', '41'])).
% 10.21/10.43  thf('43', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.21/10.43         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['42'])).
% 10.21/10.43  thf('44', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X4 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             (k5_relat_1 @ X3 @ X0))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ X4 @ 
% 10.21/10.43                (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43                 (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 10.21/10.43               X3))),
% 10.21/10.43      inference('sup-', [status(thm)], ['38', '43'])).
% 10.21/10.43  thf('45', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.21/10.43         (~ (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X4 @ 
% 10.21/10.43              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X4 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 10.21/10.43             (k5_relat_1 @ X3 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['44'])).
% 10.21/10.43  thf('46', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1) @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))) @ 
% 10.21/10.43             (k5_relat_1 @ X0 @ X2)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['31', '45'])).
% 10.21/10.43  thf('47', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_F_1 @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43             (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ X1) @ 
% 10.21/10.43            (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))) @ 
% 10.21/10.43           (k5_relat_1 @ X0 @ X2))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['46'])).
% 10.21/10.43  thf('48', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_F_1 @ 
% 10.21/10.43                (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43                X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43               (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ 
% 10.21/10.43               X1) @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))) @ 
% 10.21/10.43             (k5_relat_1 @ X0 @ X2)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['23', '47'])).
% 10.21/10.43  thf('49', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_F_1 @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X2 @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0)) @ 
% 10.21/10.43             (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ X0 @ X1) @ 
% 10.21/10.43            (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))) @ 
% 10.21/10.43           (k5_relat_1 @ X0 @ X2))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['48'])).
% 10.21/10.43  thf('50', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.21/10.43         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['42'])).
% 10.21/10.43  thf('51', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X4)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X5 @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))) @ 
% 10.21/10.43             (k5_relat_1 @ X4 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ X5 @ 
% 10.21/10.43                (sk_F_1 @ 
% 10.21/10.43                 (sk_F_1 @ 
% 10.21/10.43                  (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43                  (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43                  X0 @ (k5_relat_1 @ X2 @ X1)) @ 
% 10.21/10.43                 (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43                 X1 @ X2)) @ 
% 10.21/10.43               X4))),
% 10.21/10.43      inference('sup-', [status(thm)], ['49', '50'])).
% 10.21/10.43  thf('52', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ X2) @ X3)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ X2)) @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ X2))) @ 
% 10.21/10.43             (k5_relat_1 @ X0 @ (k5_relat_1 @ X1 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X2))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['22', '51'])).
% 10.21/10.43  thf('53', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X2))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ X2)) @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ X2))) @ 
% 10.21/10.43             (k5_relat_1 @ X0 @ (k5_relat_1 @ X1 @ X2)))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ X2) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('simplify', [status(thm)], ['52'])).
% 10.21/10.43  thf('54', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X3)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43              (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 10.21/10.43      inference('sup-', [status(thm)], ['8', '53'])).
% 10.21/10.43  thf('55', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_C @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43            (sk_D @ X3 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))) @ 
% 10.21/10.43           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['54'])).
% 10.21/10.43  thf('56', plain,
% 10.21/10.43      (![X6 : $i, X7 : $i]:
% 10.21/10.43         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D @ X6 @ X7)) @ X6)
% 10.21/10.43          | (r1_tarski @ X7 @ X6)
% 10.21/10.43          | ~ (v1_relat_1 @ X7))),
% 10.21/10.43      inference('cnf', [status(esa)], [d3_relat_1])).
% 10.21/10.43  thf('57', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 10.21/10.43      inference('sup-', [status(thm)], ['55', '56'])).
% 10.21/10.43  thf('58', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['57'])).
% 10.21/10.43  thf('59', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 10.21/10.43      inference('sup-', [status(thm)], ['7', '58'])).
% 10.21/10.43  thf('60', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['59'])).
% 10.21/10.43  thf('61', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2))))),
% 10.21/10.43      inference('sup-', [status(thm)], ['6', '60'])).
% 10.21/10.43  thf('62', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43           (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['61'])).
% 10.21/10.43  thf('63', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('64', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('65', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('66', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('67', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('68', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X11)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 10.21/10.43             X13)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_F @ X13 @ X11 @ X12)) @ 
% 10.21/10.43             X12)
% 10.21/10.43          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (v1_relat_1 @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X12))),
% 10.21/10.43      inference('cnf', [status(esa)], [d8_relat_1])).
% 10.21/10.43  thf('69', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('70', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X11)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 10.21/10.43             X13)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 10.21/10.43             X11)
% 10.21/10.43          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (v1_relat_1 @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X12))),
% 10.21/10.43      inference('cnf', [status(esa)], [d8_relat_1])).
% 10.21/10.43  thf('71', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X14 @ (sk_F_1 @ X17 @ X14 @ X11 @ X12)) @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['12'])).
% 10.21/10.43  thf('72', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['70', '71'])).
% 10.21/10.43  thf('73', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2))),
% 10.21/10.43      inference('simplify', [status(thm)], ['72'])).
% 10.21/10.43  thf('74', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1)) @ 
% 10.21/10.43             X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['69', '73'])).
% 10.21/10.43  thf('75', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43            (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1)) @ 
% 10.21/10.43           X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['74'])).
% 10.21/10.43  thf('76', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.21/10.43         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['42'])).
% 10.21/10.43  thf('77', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X0 @ X1)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X4)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X5 @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2) @ X1 @ X0)) @ 
% 10.21/10.43             (k5_relat_1 @ X4 @ X0))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ X5 @ (sk_F @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2)) @ 
% 10.21/10.43               X4))),
% 10.21/10.43      inference('sup-', [status(thm)], ['75', '76'])).
% 10.21/10.43  thf('78', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.21/10.43         (~ (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X5 @ (sk_F @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2)) @ X4)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X5 @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2) @ X1 @ X0)) @ 
% 10.21/10.43             (k5_relat_1 @ X4 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X4)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X1) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X0 @ X1)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('simplify', [status(thm)], ['77'])).
% 10.21/10.43  thf('79', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X0 @ (k5_relat_1 @ X2 @ X1)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X0 @ (k5_relat_1 @ X2 @ X1)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X1 @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ X0 @ X2)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['68', '78'])).
% 10.21/10.43  thf('80', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43            (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (sk_F @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X1 @ X2)) @ 
% 10.21/10.43           (k5_relat_1 @ X0 @ X2))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X2 @ X1) @ X0)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X0 @ (k5_relat_1 @ X2 @ X1)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['79'])).
% 10.21/10.43  thf('81', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ X1)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['67', '80'])).
% 10.21/10.43  thf('82', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43            (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1)) @ 
% 10.21/10.43           (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['81'])).
% 10.21/10.43  thf('83', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('84', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X11)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 10.21/10.43             X13)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 10.21/10.43             X11)
% 10.21/10.43          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (v1_relat_1 @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X12))),
% 10.21/10.43      inference('cnf', [status(esa)], [d8_relat_1])).
% 10.21/10.43  thf('85', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['26'])).
% 10.21/10.43  thf('86', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['84', '85'])).
% 10.21/10.43  thf('87', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2))),
% 10.21/10.43      inference('simplify', [status(thm)], ['86'])).
% 10.21/10.43  thf('88', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['83', '87'])).
% 10.21/10.43  thf('89', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (sk_F @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ X0 @ X1) @ 
% 10.21/10.43            (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43           X0)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['88'])).
% 10.21/10.43  thf('90', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.21/10.43         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['42'])).
% 10.21/10.43  thf('91', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X1 @ (k5_relat_1 @ X2 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X4)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X5 @ (sk_E @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ X4 @ X0))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ X5 @ 
% 10.21/10.43                (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1) @ 
% 10.21/10.43                 (sk_F @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1) @ X0 @ X2)) @ 
% 10.21/10.43               X4))),
% 10.21/10.43      inference('sup-', [status(thm)], ['89', '90'])).
% 10.21/10.43  thf('92', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.21/10.43         (~ (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X5 @ 
% 10.21/10.43              (sk_F_1 @ (sk_E @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1) @ 
% 10.21/10.43               (sk_F @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1) @ X0 @ X2)) @ 
% 10.21/10.43             X4)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X5 @ (sk_E @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ X4 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X4)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X2 @ X0) @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X1 @ (k5_relat_1 @ X2 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['91'])).
% 10.21/10.43  thf('93', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['82', '92'])).
% 10.21/10.43  thf('94', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43            (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43           (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2))),
% 10.21/10.43      inference('simplify', [status(thm)], ['93'])).
% 10.21/10.43  thf('95', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['66', '94'])).
% 10.21/10.43  thf('96', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43            (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43           (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_D_1 @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ X3 @ (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((X3) = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['95'])).
% 10.21/10.43  thf('97', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)))),
% 10.21/10.43      inference('eq_fact', [status(thm)], ['96'])).
% 10.21/10.43  thf('98', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['65', '97'])).
% 10.21/10.43  thf('99', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['98'])).
% 10.21/10.43  thf('100', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('sup-', [status(thm)], ['64', '99'])).
% 10.21/10.43  thf('101', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['100'])).
% 10.21/10.43  thf('102', plain,
% 10.21/10.43      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 10.21/10.43         (~ (r1_tarski @ X7 @ X8)
% 10.21/10.43          | (r2_hidden @ (k4_tarski @ X9 @ X10) @ X8)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X7)
% 10.21/10.43          | ~ (v1_relat_1 @ X7))),
% 10.21/10.43      inference('cnf', [status(esa)], [d3_relat_1])).
% 10.21/10.43  thf('103', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X3))),
% 10.21/10.43      inference('sup-', [status(thm)], ['101', '102'])).
% 10.21/10.43  thf('104', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X3)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['63', '103'])).
% 10.21/10.43  thf('105', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X3)
% 10.21/10.43          | ~ (r1_tarski @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ X3)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['104'])).
% 10.21/10.43  thf('106', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['62', '105'])).
% 10.21/10.43  thf('107', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43            = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('simplify', [status(thm)], ['106'])).
% 10.21/10.43  thf('108', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2))))),
% 10.21/10.43      inference('sup-', [status(thm)], ['5', '107'])).
% 10.21/10.43  thf('109', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['108'])).
% 10.21/10.43  thf('110', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ X14 @ (sk_F_1 @ X17 @ X14 @ X11 @ X12)) @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['12'])).
% 10.21/10.43  thf('111', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2))),
% 10.21/10.43      inference('sup-', [status(thm)], ['109', '110'])).
% 10.21/10.43  thf('112', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('simplify', [status(thm)], ['111'])).
% 10.21/10.43  thf('113', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X2))),
% 10.21/10.43      inference('sup-', [status(thm)], ['4', '112'])).
% 10.21/10.43  thf('114', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43           X2)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('simplify', [status(thm)], ['113'])).
% 10.21/10.43  thf('115', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             X2))),
% 10.21/10.43      inference('sup-', [status(thm)], ['3', '114'])).
% 10.21/10.43  thf('116', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43           X2)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['115'])).
% 10.21/10.43  thf('117', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('118', plain,
% 10.21/10.43      (![X19 : $i, X20 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X19)
% 10.21/10.43          | ~ (v1_relat_1 @ X20)
% 10.21/10.43          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 10.21/10.43      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 10.21/10.43  thf('119', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['108'])).
% 10.21/10.43  thf('120', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X12)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 10.21/10.43          | ~ (v1_relat_1 @ X11))),
% 10.21/10.43      inference('simplify', [status(thm)], ['26'])).
% 10.21/10.43  thf('121', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2))),
% 10.21/10.43      inference('sup-', [status(thm)], ['119', '120'])).
% 10.21/10.43  thf('122', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('simplify', [status(thm)], ['121'])).
% 10.21/10.43  thf('123', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['118', '122'])).
% 10.21/10.43  thf('124', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43            (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43           (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('simplify', [status(thm)], ['123'])).
% 10.21/10.43  thf('125', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_F_1 @ 
% 10.21/10.43               (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['117', '124'])).
% 10.21/10.43  thf('126', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         ((r2_hidden @ 
% 10.21/10.43           (k4_tarski @ 
% 10.21/10.43            (sk_F_1 @ 
% 10.21/10.43             (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43              (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43            (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43             (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43           (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['125'])).
% 10.21/10.43  thf('127', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | (r2_hidden @ 
% 10.21/10.43             (k4_tarski @ 
% 10.21/10.43              (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1) @ 
% 10.21/10.43              (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43               (k5_relat_1 @ X0 @ X2) @ X1)) @ 
% 10.21/10.43             (k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['100'])).
% 10.21/10.43  thf('128', plain,
% 10.21/10.43      (![X11 : $i, X12 : $i, X13 : $i, X18 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X11)
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ 
% 10.21/10.43                (sk_E @ X13 @ X11 @ X12)) @ 
% 10.21/10.43               X13)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ X18 @ (sk_E @ X13 @ X11 @ X12)) @ X11)
% 10.21/10.43          | ~ (r2_hidden @ (k4_tarski @ (sk_D_1 @ X13 @ X11 @ X12) @ X18) @ X12)
% 10.21/10.43          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 10.21/10.43          | ~ (v1_relat_1 @ X13)
% 10.21/10.43          | ~ (v1_relat_1 @ X12))),
% 10.21/10.43      inference('cnf', [status(esa)], [d8_relat_1])).
% 10.21/10.43  thf('129', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ 
% 10.21/10.43                (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                X3) @ 
% 10.21/10.43               X2)
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ X3 @ 
% 10.21/10.43                (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['127', '128'])).
% 10.21/10.43  thf('130', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ X3 @ 
% 10.21/10.43                (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43               (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ 
% 10.21/10.43                (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                X3) @ 
% 10.21/10.43               X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('simplify', [status(thm)], ['129'])).
% 10.21/10.43  thf('131', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ 
% 10.21/10.43                (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                (sk_F_1 @ 
% 10.21/10.43                 (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                  (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                 (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                  (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43               X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['126', '130'])).
% 10.21/10.43  thf('132', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ~ (r2_hidden @ 
% 10.21/10.43               (k4_tarski @ 
% 10.21/10.43                (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                (sk_F_1 @ 
% 10.21/10.43                 (sk_E @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                  (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                 (sk_D_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0) @ 
% 10.21/10.43                  (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 10.21/10.43                 (k5_relat_1 @ X1 @ X0) @ X2)) @ 
% 10.21/10.43               X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['131'])).
% 10.21/10.43  thf('133', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ X2) @ X1)
% 10.21/10.43              = (k5_relat_1 @ X0 @ (k5_relat_1 @ X2 @ X1)))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ X2) @ X1)
% 10.21/10.43              = (k5_relat_1 @ X0 @ (k5_relat_1 @ X2 @ X1)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X2) @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['116', '132'])).
% 10.21/10.43  thf('134', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ X0 @ X2) @ X1))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ X2) @ X1)
% 10.21/10.43              = (k5_relat_1 @ X0 @ (k5_relat_1 @ X2 @ X1)))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1))),
% 10.21/10.43      inference('simplify', [status(thm)], ['133'])).
% 10.21/10.43  thf('135', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.21/10.43      inference('sup-', [status(thm)], ['2', '134'])).
% 10.21/10.43  thf('136', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['135'])).
% 10.21/10.43  thf('137', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43              = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 10.21/10.43      inference('sup-', [status(thm)], ['1', '136'])).
% 10.21/10.43  thf('138', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 10.21/10.43            = (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['137'])).
% 10.21/10.43  thf('139', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X0)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2))))),
% 10.21/10.43      inference('sup-', [status(thm)], ['0', '138'])).
% 10.21/10.43  thf('140', plain,
% 10.21/10.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.21/10.43         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 10.21/10.43            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 10.21/10.43          | ~ (v1_relat_1 @ X2)
% 10.21/10.43          | ~ (v1_relat_1 @ X1)
% 10.21/10.43          | ~ (v1_relat_1 @ X0))),
% 10.21/10.43      inference('simplify', [status(thm)], ['139'])).
% 10.21/10.43  thf(t55_relat_1, conjecture,
% 10.21/10.43    (![A:$i]:
% 10.21/10.43     ( ( v1_relat_1 @ A ) =>
% 10.21/10.43       ( ![B:$i]:
% 10.21/10.43         ( ( v1_relat_1 @ B ) =>
% 10.21/10.43           ( ![C:$i]:
% 10.21/10.43             ( ( v1_relat_1 @ C ) =>
% 10.21/10.43               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 10.21/10.43                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 10.21/10.43  thf(zf_stmt_0, negated_conjecture,
% 10.21/10.43    (~( ![A:$i]:
% 10.21/10.43        ( ( v1_relat_1 @ A ) =>
% 10.21/10.43          ( ![B:$i]:
% 10.21/10.43            ( ( v1_relat_1 @ B ) =>
% 10.21/10.43              ( ![C:$i]:
% 10.21/10.43                ( ( v1_relat_1 @ C ) =>
% 10.21/10.43                  ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 10.21/10.43                    ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 10.21/10.43    inference('cnf.neg', [status(esa)], [t55_relat_1])).
% 10.21/10.43  thf('141', plain,
% 10.21/10.43      (((k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C_1)
% 10.21/10.43         != (k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_C_1)))),
% 10.21/10.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.21/10.43  thf('142', plain,
% 10.21/10.43      ((((k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_C_1))
% 10.21/10.43          != (k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_C_1)))
% 10.21/10.43        | ~ (v1_relat_1 @ sk_B)
% 10.21/10.43        | ~ (v1_relat_1 @ sk_A)
% 10.21/10.43        | ~ (v1_relat_1 @ sk_C_1))),
% 10.21/10.43      inference('sup-', [status(thm)], ['140', '141'])).
% 10.21/10.43  thf('143', plain, ((v1_relat_1 @ sk_B)),
% 10.21/10.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.21/10.43  thf('144', plain, ((v1_relat_1 @ sk_A)),
% 10.21/10.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.21/10.43  thf('145', plain, ((v1_relat_1 @ sk_C_1)),
% 10.21/10.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.21/10.43  thf('146', plain,
% 10.21/10.43      (((k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_C_1))
% 10.21/10.43         != (k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_C_1)))),
% 10.21/10.43      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 10.21/10.43  thf('147', plain, ($false), inference('simplify', [status(thm)], ['146'])).
% 10.21/10.43  
% 10.21/10.43  % SZS output end Refutation
% 10.21/10.43  
% 10.21/10.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
