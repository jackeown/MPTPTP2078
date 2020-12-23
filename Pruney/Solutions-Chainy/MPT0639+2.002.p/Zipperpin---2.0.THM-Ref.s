%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6UwSw0baRR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:11 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 186 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   35
%              Number of atoms          : 2113 (3362 expanded)
%              Number of equality atoms :   48 (  67 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_B @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_B @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X2 ) @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X2 ) @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('26',plain,(
    ! [X2: $i] :
      ( ( ( k1_funct_1 @ X2 @ ( sk_B @ X2 ) )
        = ( k1_funct_1 @ X2 @ ( sk_C @ X2 ) ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X2 ) @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X2 ) @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ X0 @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('49',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) )
      | ( ( k1_funct_1 @ X2 @ X3 )
       != ( k1_funct_1 @ X2 @ X4 ) )
      | ( X3 = X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = X2 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = X2 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = X2 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = X2 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('65',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) )
      | ( ( k1_funct_1 @ X2 @ X3 )
       != ( k1_funct_1 @ X2 @ X4 ) )
      | ( X3 = X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) )
        = X2 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) )
        = X2 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
       != ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) )
        = X2 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ( ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) )
        = X2 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
       != ( k1_funct_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(eq_res,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t46_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( v2_funct_1 @ B ) )
             => ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_funct_1])).

thf('73',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( ( sk_C @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
      = ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_C @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    = ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79','80'])).

thf('82',plain,(
    ! [X2: $i] :
      ( ( ( sk_B @ X2 )
       != ( sk_C @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('83',plain,
    ( ( ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
     != ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6UwSw0baRR
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:08:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 116 iterations in 0.196s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i > $i).
% 0.45/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.66  thf(fc2_funct_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.45/0.66         ( v1_funct_1 @ B ) ) =>
% 0.45/0.66       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.45/0.66         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X6)
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.45/0.66  thf(dt_k5_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.45/0.66       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X6)
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.66  thf(d8_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v2_funct_1 @ A ) <=>
% 0.45/0.66         ( ![B:$i,C:$i]:
% 0.45/0.66           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.45/0.66               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.45/0.66               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.45/0.66             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X2 : $i]:
% 0.45/0.66         ((r2_hidden @ (sk_B @ X2) @ (k1_relat_1 @ X2))
% 0.45/0.66          | (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf(t21_funct_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.66           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.45/0.66             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.66               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X7)
% 0.45/0.66          | ~ (v1_funct_1 @ X7)
% 0.45/0.66          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.45/0.66          | (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '6'])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X6)
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X2 : $i]:
% 0.45/0.66         ((r2_hidden @ (sk_B @ X2) @ (k1_relat_1 @ X2))
% 0.45/0.66          | (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X7)
% 0.45/0.66          | ~ (v1_funct_1 @ X7)
% 0.45/0.66          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['12', '15'])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['11', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.66  thf(t23_funct_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.66           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.45/0.66             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.45/0.66               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X10)
% 0.45/0.66          | ~ (v1_funct_1 @ X10)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 0.45/0.66              = (k1_funct_1 @ X10 @ (k1_funct_1 @ X11 @ X12)))
% 0.45/0.66          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.45/0.66          | ~ (v1_funct_1 @ X11)
% 0.45/0.66          | ~ (v1_relat_1 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X2) @ 
% 0.45/0.66              (sk_B @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66              = (k1_funct_1 @ X2 @ 
% 0.45/0.66                 (k1_funct_1 @ X0 @ (sk_B @ (k5_relat_1 @ X0 @ X1)))))
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X2) @ 
% 0.45/0.66              (sk_B @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66              = (k1_funct_1 @ X2 @ 
% 0.45/0.66                 (k1_funct_1 @ X0 @ (sk_B @ (k5_relat_1 @ X0 @ X1)))))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X6)
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X2 : $i]:
% 0.45/0.66         (((k1_funct_1 @ X2 @ (sk_B @ X2)) = (k1_funct_1 @ X2 @ (sk_C @ X2)))
% 0.45/0.66          | (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X6)
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X2 : $i]:
% 0.45/0.66         ((r2_hidden @ (sk_C @ X2) @ (k1_relat_1 @ X2))
% 0.45/0.66          | (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X7)
% 0.45/0.66          | ~ (v1_funct_1 @ X7)
% 0.45/0.66          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.45/0.66          | (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['28', '31'])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X10)
% 0.45/0.66          | ~ (v1_funct_1 @ X10)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 0.45/0.66              = (k1_funct_1 @ X10 @ (k1_funct_1 @ X11 @ X12)))
% 0.45/0.66          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.45/0.66          | ~ (v1_funct_1 @ X11)
% 0.45/0.66          | ~ (v1_relat_1 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X2) @ 
% 0.45/0.66              (sk_C @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66              = (k1_funct_1 @ X2 @ 
% 0.45/0.66                 (k1_funct_1 @ X0 @ (sk_C @ (k5_relat_1 @ X0 @ X1)))))
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X2) @ 
% 0.45/0.66              (sk_C @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66              = (k1_funct_1 @ X2 @ 
% 0.45/0.66                 (k1_funct_1 @ X0 @ (sk_C @ (k5_relat_1 @ X0 @ X1)))))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.45/0.66            (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66            = (k1_funct_1 @ X0 @ 
% 0.45/0.66               (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.45/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['26', '38'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.45/0.66              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              = (k1_funct_1 @ X0 @ 
% 0.45/0.66                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.45/0.66              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              = (k1_funct_1 @ X0 @ 
% 0.45/0.66                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.45/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['25', '40'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.45/0.66              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              = (k1_funct_1 @ X0 @ 
% 0.45/0.66                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.45/0.66              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              = (k1_funct_1 @ X0 @ 
% 0.45/0.66                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['24', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.45/0.66              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              = (k1_funct_1 @ X0 @ 
% 0.45/0.66                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['43'])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_funct_1 @ X0 @ 
% 0.45/0.66            (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66            = (k1_funct_1 @ X0 @ 
% 0.45/0.66               (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['23', '44'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ X0 @ 
% 0.45/0.66              (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66              = (k1_funct_1 @ X0 @ 
% 0.45/0.66                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X6)
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X2 : $i]:
% 0.45/0.66         ((r2_hidden @ (sk_C @ X2) @ (k1_relat_1 @ X2))
% 0.45/0.66          | (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X7)
% 0.45/0.66          | ~ (v1_funct_1 @ X7)
% 0.45/0.66          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['48', '51'])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['52'])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['47', '53'])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['54'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.45/0.66          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X2))
% 0.45/0.66          | ((k1_funct_1 @ X2 @ X3) != (k1_funct_1 @ X2 @ X4))
% 0.45/0.66          | ((X3) = (X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.45/0.66          | ((k1_funct_1 @ X0 @ 
% 0.45/0.66              (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66              != (k1_funct_1 @ X0 @ X2))
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ X0 @ 
% 0.45/0.66              (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66              != (k1_funct_1 @ X0 @ X2))
% 0.45/0.66          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['57'])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k1_funct_1 @ X0 @ 
% 0.45/0.66            (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66            != (k1_funct_1 @ X0 @ X2))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['46', '58'])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ X0 @ 
% 0.45/0.66              (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66              != (k1_funct_1 @ X0 @ X2)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['59'])).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              = (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66          | ~ (r2_hidden @ 
% 0.45/0.66               (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66               (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['60'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              = (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '61'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66            = (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['62'])).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.45/0.66          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X2))
% 0.45/0.66          | ((k1_funct_1 @ X2 @ X3) != (k1_funct_1 @ X2 @ X4))
% 0.45/0.66          | ((X3) = (X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (X2))
% 0.45/0.66          | ((k1_funct_1 @ X0 @ (sk_C @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66              != (k1_funct_1 @ X0 @ X2))
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.45/0.66          | ((k1_funct_1 @ X0 @ (sk_C @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66              != (k1_funct_1 @ X0 @ X2))
% 0.45/0.66          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (X2))
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66            != (k1_funct_1 @ X1 @ X2))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ((sk_C @ (k5_relat_1 @ X1 @ X0)) = (X2))
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v2_funct_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['63', '67'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X1)
% 0.45/0.66          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.45/0.66          | ((sk_C @ (k5_relat_1 @ X1 @ X0)) = (X2))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66              != (k1_funct_1 @ X1 @ X2)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['68'])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((sk_C @ (k5_relat_1 @ X1 @ X0)) = (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.45/0.66          | ~ (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.45/0.66          | ~ (v2_funct_1 @ X1))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['69'])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (sk_B @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66          | ~ (v2_funct_1 @ X1)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '70'])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X1)
% 0.45/0.66          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (sk_B @ (k5_relat_1 @ X0 @ X1)))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ X1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.66  thf(t46_funct_1, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.45/0.66             ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66              ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.45/0.66                ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t46_funct_1])).
% 0.45/0.66  thf('73', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_A)
% 0.45/0.66        | ((sk_C @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66            = (sk_B @ (k5_relat_1 @ sk_A @ sk_B_1)))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.66  thf('75', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('76', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('78', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('79', plain, ((v2_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('80', plain, ((v2_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      (((sk_C @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66         = (sk_B @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)],
% 0.45/0.66                ['74', '75', '76', '77', '78', '79', '80'])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      (![X2 : $i]:
% 0.45/0.66         (((sk_B @ X2) != (sk_C @ X2))
% 0.45/0.66          | (v2_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_funct_1 @ X2)
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      ((((sk_B @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66          != (sk_B @ (k5_relat_1 @ sk_A @ sk_B_1)))
% 0.45/0.66        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (((v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['83'])).
% 0.45/0.66  thf('85', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.45/0.66        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('clc', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '86'])).
% 0.45/0.66  thf('88', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('90', plain, (~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B_1)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '90'])).
% 0.45/0.66  thf('92', plain, ((v1_funct_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('93', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('94', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('95', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('96', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
