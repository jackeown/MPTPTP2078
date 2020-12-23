%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0577+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bl7QePZukc

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:08 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 244 expanded)
%              Number of leaves         :   16 (  64 expanded)
%              Depth                    :   34
%              Number of atoms          : 2401 (6608 expanded)
%              Number of equality atoms :   65 ( 189 expanded)
%              Maximal formula depth    :   27 (  14 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( sk_E @ X0 @ X1 @ X2 ) @ X1 )
      | ( X0
        = ( k10_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X2 ) @ ( sk_E @ X0 @ X1 @ X2 ) ) @ X2 )
      | ( X0
        = ( k10_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

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

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( X10
       != ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) @ X14 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) @ X14 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X2 ) @ ( sk_E @ X0 @ X1 @ X2 ) ) @ X2 )
      | ( X0
        = ( k10_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( X10
       != ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X4 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_F_1 @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X3 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 )
      | ( X3
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( X10
       != ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X12 ) @ X8 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('52',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X12 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k5_relat_1 @ X9 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k10_relat_1 @ X2 @ X1 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X0 @ ( k10_relat_1 @ X2 @ X1 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( k10_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k10_relat_1 @ X2 @ X1 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X2 ) @ X3 ) @ X2 )
      | ( X0
        = ( k10_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) @ X2 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_E_1 @ ( sk_D @ ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) @ X2 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k10_relat_1 @ X0 @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(t181_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t181_relat_1])).

thf('68',plain,(
    ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
     != ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).


%------------------------------------------------------------------------------
