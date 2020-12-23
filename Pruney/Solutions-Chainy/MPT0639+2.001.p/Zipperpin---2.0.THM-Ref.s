%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.10SwrnzhWT

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:11 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 224 expanded)
%              Number of leaves         :   17 (  69 expanded)
%              Depth                    :   39
%              Number of atoms          : 2429 (4198 expanded)
%              Number of equality atoms :   48 (  71 expanded)
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

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) @ X12 )
        = ( k1_funct_1 @ X11 @ ( k1_funct_1 @ X10 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( ( k1_funct_1 @ X2 @ ( sk_B @ X2 ) )
        = ( k1_funct_1 @ X2 @ ( sk_C @ X2 ) ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
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
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
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
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
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
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) @ X12 )
        = ( k1_funct_1 @ X11 @ ( k1_funct_1 @ X10 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
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
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','58'])).

thf('60',plain,(
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
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
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
    inference('sup-',[status(thm)],['31','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['30','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('68',plain,(
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

thf('69',plain,(
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
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
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
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
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
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
    inference(eq_res,[status(thm)],['72'])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['19','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('77',plain,(
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

thf('78',plain,(
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
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
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
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
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
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
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
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
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
    inference(eq_res,[status(thm)],['81'])).

thf('83',plain,(
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
    inference('sup-',[status(thm)],['10','82'])).

thf('84',plain,(
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
    inference(simplify,[status(thm)],['83'])).

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

thf('85',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( ( sk_C @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
      = ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_C @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    = ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91','92'])).

thf('94',plain,(
    ! [X2: $i] :
      ( ( ( sk_B @ X2 )
       != ( sk_C @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('95',plain,
    ( ( ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
     != ( sk_B @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.10SwrnzhWT
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.43/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.69  % Solved by: fo/fo7.sh
% 0.43/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.69  % done 119 iterations in 0.222s
% 0.43/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.69  % SZS output start Refutation
% 0.43/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.43/0.69  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.43/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.69  thf(sk_C_type, type, sk_C: $i > $i).
% 0.43/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.69  thf(fc2_funct_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.43/0.69         ( v1_funct_1 @ B ) ) =>
% 0.43/0.69       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.43/0.69         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.43/0.69  thf('0', plain,
% 0.43/0.69      (![X5 : $i, X6 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X6)
% 0.43/0.69          | ~ (v1_funct_1 @ X6)
% 0.43/0.69          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.43/0.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.43/0.69  thf(dt_k5_relat_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.43/0.69       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.43/0.69  thf('1', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.43/0.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.69  thf('2', plain,
% 0.43/0.69      (![X5 : $i, X6 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X6)
% 0.43/0.69          | ~ (v1_funct_1 @ X6)
% 0.43/0.69          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.43/0.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.43/0.69  thf('3', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.43/0.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.69  thf(d8_funct_1, axiom,
% 0.43/0.69    (![A:$i]:
% 0.43/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.69       ( ( v2_funct_1 @ A ) <=>
% 0.43/0.69         ( ![B:$i,C:$i]:
% 0.43/0.69           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.43/0.69               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.43/0.69               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.43/0.69             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.43/0.69  thf('4', plain,
% 0.43/0.69      (![X2 : $i]:
% 0.43/0.69         ((r2_hidden @ (sk_B @ X2) @ (k1_relat_1 @ X2))
% 0.43/0.69          | (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf(t21_funct_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.69       ( ![C:$i]:
% 0.43/0.69         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.69           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.43/0.69             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.43/0.69               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.43/0.69  thf('5', plain,
% 0.43/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X7)
% 0.43/0.69          | ~ (v1_funct_1 @ X7)
% 0.43/0.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.43/0.69          | (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.43/0.69          | ~ (v1_funct_1 @ X9)
% 0.43/0.69          | ~ (v1_relat_1 @ X9))),
% 0.43/0.69      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.43/0.69  thf('6', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.69  thf('7', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['3', '6'])).
% 0.43/0.69  thf('8', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['7'])).
% 0.43/0.69  thf('9', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['2', '8'])).
% 0.43/0.69  thf('10', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.69  thf('11', plain,
% 0.43/0.69      (![X5 : $i, X6 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X6)
% 0.43/0.69          | ~ (v1_funct_1 @ X6)
% 0.43/0.69          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.43/0.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.43/0.69  thf('12', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.43/0.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.69  thf('13', plain,
% 0.43/0.69      (![X2 : $i]:
% 0.43/0.69         ((r2_hidden @ (sk_B @ X2) @ (k1_relat_1 @ X2))
% 0.43/0.69          | (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf('14', plain,
% 0.43/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X7)
% 0.43/0.69          | ~ (v1_funct_1 @ X7)
% 0.43/0.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.43/0.69          | ~ (v1_funct_1 @ X9)
% 0.43/0.69          | ~ (v1_relat_1 @ X9))),
% 0.43/0.69      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.43/0.69  thf('15', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.69  thf('16', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['12', '15'])).
% 0.43/0.69  thf('17', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.43/0.69  thf('18', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['11', '17'])).
% 0.43/0.69  thf('19', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['18'])).
% 0.43/0.69  thf('20', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.69  thf('21', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['18'])).
% 0.43/0.69  thf('22', plain,
% 0.43/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X7)
% 0.43/0.69          | ~ (v1_funct_1 @ X7)
% 0.43/0.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.43/0.69          | ~ (r2_hidden @ (k1_funct_1 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.43/0.69          | (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.43/0.69          | ~ (v1_funct_1 @ X9)
% 0.43/0.69          | ~ (v1_relat_1 @ X9))),
% 0.43/0.69      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.43/0.69  thf('23', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.43/0.69             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69          | ~ (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.69  thf('24', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.43/0.69             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.43/0.69  thf('25', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | (r2_hidden @ (sk_B @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.43/0.69             (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.43/0.69      inference('sup-', [status(thm)], ['20', '24'])).
% 0.43/0.69  thf('26', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((r2_hidden @ (sk_B @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.43/0.69           (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1))),
% 0.43/0.69      inference('simplify', [status(thm)], ['25'])).
% 0.43/0.69  thf(t22_funct_1, axiom,
% 0.43/0.69    (![A:$i,B:$i]:
% 0.43/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.69       ( ![C:$i]:
% 0.43/0.69         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.69           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.43/0.69             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.43/0.69               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.43/0.69  thf('27', plain,
% 0.43/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X10)
% 0.43/0.69          | ~ (v1_funct_1 @ X10)
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X10 @ X11) @ X12)
% 0.43/0.69              = (k1_funct_1 @ X11 @ (k1_funct_1 @ X10 @ X12)))
% 0.43/0.69          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X10 @ X11)))
% 0.43/0.69          | ~ (v1_funct_1 @ X11)
% 0.43/0.69          | ~ (v1_relat_1 @ X11))),
% 0.43/0.69      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.43/0.69  thf('28', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['26', '27'])).
% 0.43/0.69  thf('29', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69            (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69            = (k1_funct_1 @ X0 @ 
% 0.43/0.69               (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['28'])).
% 0.43/0.69  thf('30', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.43/0.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.69  thf('31', plain,
% 0.43/0.69      (![X5 : $i, X6 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X6)
% 0.43/0.69          | ~ (v1_funct_1 @ X6)
% 0.43/0.69          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.43/0.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.43/0.69  thf('32', plain,
% 0.43/0.69      (![X2 : $i]:
% 0.43/0.69         (((k1_funct_1 @ X2 @ (sk_B @ X2)) = (k1_funct_1 @ X2 @ (sk_C @ X2)))
% 0.43/0.69          | (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf('33', plain,
% 0.43/0.69      (![X5 : $i, X6 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X6)
% 0.43/0.69          | ~ (v1_funct_1 @ X6)
% 0.43/0.69          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.43/0.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.43/0.69  thf('34', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.43/0.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.69  thf('35', plain,
% 0.43/0.69      (![X2 : $i]:
% 0.43/0.69         ((r2_hidden @ (sk_C @ X2) @ (k1_relat_1 @ X2))
% 0.43/0.69          | (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf('36', plain,
% 0.43/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X7)
% 0.43/0.69          | ~ (v1_funct_1 @ X7)
% 0.43/0.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.43/0.69          | (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.43/0.69          | ~ (v1_funct_1 @ X9)
% 0.43/0.69          | ~ (v1_relat_1 @ X9))),
% 0.43/0.69      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.43/0.69  thf('37', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.43/0.69  thf('38', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['34', '37'])).
% 0.43/0.69  thf('39', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['38'])).
% 0.43/0.69  thf('40', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['33', '39'])).
% 0.43/0.69  thf('41', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['40'])).
% 0.43/0.69  thf('42', plain,
% 0.43/0.69      (![X5 : $i, X6 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X5)
% 0.43/0.69          | ~ (v1_relat_1 @ X6)
% 0.43/0.69          | ~ (v1_funct_1 @ X6)
% 0.43/0.69          | (v1_funct_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.43/0.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.43/0.69  thf('43', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.43/0.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.69  thf('44', plain,
% 0.43/0.69      (![X2 : $i]:
% 0.43/0.69         ((r2_hidden @ (sk_C @ X2) @ (k1_relat_1 @ X2))
% 0.43/0.69          | (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf('45', plain,
% 0.43/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X7)
% 0.43/0.69          | ~ (v1_funct_1 @ X7)
% 0.43/0.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.43/0.69          | ~ (v1_funct_1 @ X9)
% 0.43/0.69          | ~ (v1_relat_1 @ X9))),
% 0.43/0.69      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.43/0.69  thf('46', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.43/0.69  thf('47', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['43', '46'])).
% 0.43/0.69  thf('48', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['47'])).
% 0.43/0.69  thf('49', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['42', '48'])).
% 0.43/0.69  thf('50', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['49'])).
% 0.43/0.69  thf('51', plain,
% 0.43/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X7)
% 0.43/0.69          | ~ (v1_funct_1 @ X7)
% 0.43/0.69          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.43/0.69          | ~ (r2_hidden @ (k1_funct_1 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.43/0.69          | (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.43/0.69          | ~ (v1_funct_1 @ X9)
% 0.43/0.69          | ~ (v1_relat_1 @ X9))),
% 0.43/0.69      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.43/0.69  thf('52', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.43/0.69             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69          | ~ (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.43/0.69  thf('53', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.43/0.69             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['52'])).
% 0.43/0.69  thf('54', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.43/0.69             (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.43/0.69      inference('sup-', [status(thm)], ['41', '53'])).
% 0.43/0.69  thf('55', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((r2_hidden @ (sk_C @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.43/0.69           (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1))),
% 0.43/0.69      inference('simplify', [status(thm)], ['54'])).
% 0.43/0.69  thf('56', plain,
% 0.43/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X10)
% 0.43/0.69          | ~ (v1_funct_1 @ X10)
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X10 @ X11) @ X12)
% 0.43/0.69              = (k1_funct_1 @ X11 @ (k1_funct_1 @ X10 @ X12)))
% 0.43/0.69          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X10 @ X11)))
% 0.43/0.69          | ~ (v1_funct_1 @ X11)
% 0.43/0.69          | ~ (v1_relat_1 @ X11))),
% 0.43/0.69      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.43/0.69  thf('57', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69              (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['55', '56'])).
% 0.43/0.69  thf('58', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69            (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69            = (k1_funct_1 @ X0 @ 
% 0.43/0.69               (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['57'])).
% 0.43/0.69  thf('59', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69            (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69            = (k1_funct_1 @ X0 @ 
% 0.43/0.69               (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['32', '58'])).
% 0.43/0.69  thf('60', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))))),
% 0.43/0.69      inference('simplify', [status(thm)], ['59'])).
% 0.43/0.69  thf('61', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['31', '60'])).
% 0.43/0.69  thf('62', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['61'])).
% 0.43/0.69  thf('63', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['30', '62'])).
% 0.43/0.69  thf('64', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.43/0.69              (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['63'])).
% 0.43/0.69  thf('65', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (((k1_funct_1 @ X0 @ 
% 0.43/0.69            (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69            = (k1_funct_1 @ X0 @ 
% 0.43/0.69               (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.43/0.69      inference('sup+', [status(thm)], ['29', '64'])).
% 0.43/0.69  thf('66', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ((k1_funct_1 @ X0 @ 
% 0.43/0.69              (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69              = (k1_funct_1 @ X0 @ 
% 0.43/0.69                 (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))))),
% 0.43/0.69      inference('simplify', [status(thm)], ['65'])).
% 0.43/0.69  thf('67', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69             (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['49'])).
% 0.43/0.69  thf('68', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.69         (~ (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.43/0.69          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X2))
% 0.43/0.69          | ((k1_funct_1 @ X2 @ X3) != (k1_funct_1 @ X2 @ X4))
% 0.43/0.69          | ((X3) = (X4))
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf('69', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.43/0.69          | ((k1_funct_1 @ X0 @ 
% 0.43/0.69              (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69              != (k1_funct_1 @ X0 @ X2))
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v2_funct_1 @ X0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.43/0.69  thf('70', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (~ (v2_funct_1 @ X0)
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ X0 @ 
% 0.43/0.69              (k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69              != (k1_funct_1 @ X0 @ X2))
% 0.43/0.69          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['69'])).
% 0.43/0.69  thf('71', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (((k1_funct_1 @ X0 @ 
% 0.43/0.69            (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69            != (k1_funct_1 @ X0 @ X2))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v2_funct_1 @ X0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['66', '70'])).
% 0.43/0.69  thf('72', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (~ (v2_funct_1 @ X0)
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0))) = (X2))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ((k1_funct_1 @ X0 @ 
% 0.43/0.69              (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69              != (k1_funct_1 @ X0 @ X2)))),
% 0.43/0.69      inference('simplify', [status(thm)], ['71'])).
% 0.43/0.69  thf('73', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69          | ~ (r2_hidden @ 
% 0.43/0.69               (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.43/0.69               (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v2_funct_1 @ X0))),
% 0.43/0.69      inference('eq_res', [status(thm)], ['72'])).
% 0.43/0.69  thf('74', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v2_funct_1 @ X0)
% 0.43/0.69          | ((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              = (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['19', '73'])).
% 0.43/0.69  thf('75', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (((k1_funct_1 @ X1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69            = (k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0))))
% 0.43/0.69          | ~ (v2_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['74'])).
% 0.43/0.69  thf('76', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         ((v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | (r2_hidden @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0))),
% 0.43/0.69      inference('simplify', [status(thm)], ['40'])).
% 0.43/0.69  thf('77', plain,
% 0.43/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.69         (~ (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.43/0.69          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X2))
% 0.43/0.69          | ((k1_funct_1 @ X2 @ X3) != (k1_funct_1 @ X2 @ X4))
% 0.43/0.69          | ((X3) = (X4))
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf('78', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (X2))
% 0.43/0.69          | ((k1_funct_1 @ X0 @ (sk_C @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.69              != (k1_funct_1 @ X0 @ X2))
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.43/0.69          | ~ (v2_funct_1 @ X0))),
% 0.43/0.69      inference('sup-', [status(thm)], ['76', '77'])).
% 0.43/0.69  thf('79', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (~ (v2_funct_1 @ X0)
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.43/0.69          | ((k1_funct_1 @ X0 @ (sk_C @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.69              != (k1_funct_1 @ X0 @ X2))
% 0.43/0.69          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (X2))
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1))),
% 0.43/0.69      inference('simplify', [status(thm)], ['78'])).
% 0.43/0.69  thf('80', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (((k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69            != (k1_funct_1 @ X1 @ X2))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v2_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ((sk_C @ (k5_relat_1 @ X1 @ X0)) = (X2))
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v2_funct_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['75', '79'])).
% 0.43/0.69  thf('81', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.69         (~ (v2_funct_1 @ X1)
% 0.43/0.69          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.43/0.69          | ((sk_C @ (k5_relat_1 @ X1 @ X0)) = (X2))
% 0.43/0.69          | ~ (v2_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ((k1_funct_1 @ X1 @ (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69              != (k1_funct_1 @ X1 @ X2)))),
% 0.43/0.69      inference('simplify', [status(thm)], ['80'])).
% 0.43/0.69  thf('82', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.69          | ~ (v2_funct_1 @ X0)
% 0.43/0.69          | ((sk_C @ (k5_relat_1 @ X1 @ X0)) = (sk_B @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.69          | ~ (r2_hidden @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ (k1_relat_1 @ X1))
% 0.43/0.69          | ~ (v2_funct_1 @ X1))),
% 0.43/0.69      inference('eq_res', [status(thm)], ['81'])).
% 0.43/0.69  thf('83', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v1_funct_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v2_funct_1 @ X0)
% 0.43/0.69          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (sk_B @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.69          | ~ (v2_funct_1 @ X1)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['10', '82'])).
% 0.43/0.69  thf('84', plain,
% 0.43/0.69      (![X0 : $i, X1 : $i]:
% 0.43/0.69         (~ (v2_funct_1 @ X1)
% 0.43/0.69          | ((sk_C @ (k5_relat_1 @ X0 @ X1)) = (sk_B @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.69          | ~ (v2_funct_1 @ X0)
% 0.43/0.69          | (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.43/0.69          | ~ (v1_funct_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X0)
% 0.43/0.69          | ~ (v1_relat_1 @ X1)
% 0.43/0.69          | ~ (v1_funct_1 @ X1))),
% 0.43/0.69      inference('simplify', [status(thm)], ['83'])).
% 0.43/0.69  thf(t46_funct_1, conjecture,
% 0.43/0.69    (![A:$i]:
% 0.43/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.69       ( ![B:$i]:
% 0.43/0.69         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.69           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.43/0.69             ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ))).
% 0.43/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.69    (~( ![A:$i]:
% 0.43/0.69        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.69          ( ![B:$i]:
% 0.43/0.69            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.69              ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 0.43/0.69                ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) ) ) )),
% 0.43/0.69    inference('cnf.neg', [status(esa)], [t46_funct_1])).
% 0.43/0.69  thf('85', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('86', plain,
% 0.43/0.69      ((~ (v1_funct_1 @ sk_B_1)
% 0.43/0.69        | ~ (v1_relat_1 @ sk_B_1)
% 0.43/0.69        | ~ (v1_relat_1 @ sk_A)
% 0.43/0.69        | ~ (v1_funct_1 @ sk_A)
% 0.43/0.69        | ~ (v2_funct_1 @ sk_A)
% 0.43/0.69        | ((sk_C @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69            = (sk_B @ (k5_relat_1 @ sk_A @ sk_B_1)))
% 0.43/0.69        | ~ (v2_funct_1 @ sk_B_1))),
% 0.43/0.69      inference('sup-', [status(thm)], ['84', '85'])).
% 0.43/0.69  thf('87', plain, ((v1_funct_1 @ sk_B_1)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('88', plain, ((v1_relat_1 @ sk_B_1)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('90', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('91', plain, ((v2_funct_1 @ sk_A)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('92', plain, ((v2_funct_1 @ sk_B_1)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('93', plain,
% 0.43/0.69      (((sk_C @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69         = (sk_B @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.43/0.69      inference('demod', [status(thm)],
% 0.43/0.69                ['86', '87', '88', '89', '90', '91', '92'])).
% 0.43/0.69  thf('94', plain,
% 0.43/0.69      (![X2 : $i]:
% 0.43/0.69         (((sk_B @ X2) != (sk_C @ X2))
% 0.43/0.69          | (v2_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_funct_1 @ X2)
% 0.43/0.69          | ~ (v1_relat_1 @ X2))),
% 0.43/0.69      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.43/0.69  thf('95', plain,
% 0.43/0.69      ((((sk_B @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69          != (sk_B @ (k5_relat_1 @ sk_A @ sk_B_1)))
% 0.43/0.69        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69        | (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['93', '94'])).
% 0.43/0.69  thf('96', plain,
% 0.43/0.69      (((v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.43/0.69      inference('simplify', [status(thm)], ['95'])).
% 0.43/0.69  thf('97', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('98', plain,
% 0.43/0.69      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.43/0.69        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.43/0.69      inference('clc', [status(thm)], ['96', '97'])).
% 0.43/0.69  thf('99', plain,
% 0.43/0.69      ((~ (v1_relat_1 @ sk_B_1)
% 0.43/0.69        | ~ (v1_relat_1 @ sk_A)
% 0.43/0.69        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1)))),
% 0.43/0.69      inference('sup-', [status(thm)], ['1', '98'])).
% 0.43/0.69  thf('100', plain, ((v1_relat_1 @ sk_B_1)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('101', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('102', plain, (~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))),
% 0.43/0.69      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.43/0.69  thf('103', plain,
% 0.43/0.69      ((~ (v1_funct_1 @ sk_B_1)
% 0.43/0.69        | ~ (v1_relat_1 @ sk_B_1)
% 0.43/0.69        | ~ (v1_relat_1 @ sk_A)
% 0.43/0.69        | ~ (v1_funct_1 @ sk_A))),
% 0.43/0.69      inference('sup-', [status(thm)], ['0', '102'])).
% 0.43/0.69  thf('104', plain, ((v1_funct_1 @ sk_B_1)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('105', plain, ((v1_relat_1 @ sk_B_1)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('107', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.69  thf('108', plain, ($false),
% 0.43/0.69      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.43/0.69  
% 0.43/0.69  % SZS output end Refutation
% 0.43/0.69  
% 0.43/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
