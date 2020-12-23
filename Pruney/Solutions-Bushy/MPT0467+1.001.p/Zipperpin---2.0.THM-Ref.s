%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0467+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JVdWyq58ET

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:57 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 532 expanded)
%              Number of leaves         :   14 ( 134 expanded)
%              Depth                    :   55
%              Number of atoms          : 7005 (18191 expanded)
%              Number of equality atoms :  130 ( 352 expanded)
%              Maximal formula depth    :   34 (  16 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) @ X1 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) @ X1 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E @ X2 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F @ X2 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F @ X2 @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E @ X2 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_F @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ X2 @ X3 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_F_1 @ ( sk_F @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ X2 ) ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_E @ X3 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ X3 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X3 )
      | ( X3
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) ) @ X1 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) @ X2 ) @ X1 @ X0 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_D @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['57','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_D @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X3 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X3 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X4 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X4 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X3 )
      | ( ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X3 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X4 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ X7 ) @ X1 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ( ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( k5_relat_1 @ X2 @ X0 ) @ X3 ) @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( k5_relat_1 @ X2 @ X0 ) @ X3 ) @ X0 @ X2 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) ) @ X0 )
      | ( ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( sk_D @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X2 ) )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('110',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('111',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) @ X1 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X2 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) @ ( sk_F @ ( k5_relat_1 @ X1 @ X0 ) @ X3 @ X2 ) ) @ X2 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_F @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X4 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_D @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X4 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) @ ( sk_F @ ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 @ X2 ) ) @ X2 )
      | ( ( k5_relat_1 @ X4 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X3 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X4 @ X3 ) ) @ X3 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) @ X1 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ X7 ) @ X1 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ( ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( k5_relat_1 @ X2 @ X0 ) @ X3 ) @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F_1 @ ( sk_E @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( k5_relat_1 @ X2 @ X0 ) @ X3 ) @ X0 @ X2 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) @ ( sk_F @ ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['108','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['106','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_F @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ X0 @ X1 ) @ X7 ) @ X1 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_E @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ ( k5_relat_1 @ X2 @ X1 ) ) @ X3 ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['136','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_E @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

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

thf('151',plain,(
    ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C )
 != ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) )
     != ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) )
 != ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    $false ),
    inference(simplify,[status(thm)],['156'])).


%------------------------------------------------------------------------------
