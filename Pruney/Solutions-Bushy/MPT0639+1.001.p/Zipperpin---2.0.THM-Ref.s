%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0639+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kDcNStJj7i

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:14 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 224 expanded)
%              Number of leaves         :   17 (  69 expanded)
%              Depth                    :   39
%              Number of atoms          : 2429 (4198 expanded)
%              Number of equality atoms :   48 (  71 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
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
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
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
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
