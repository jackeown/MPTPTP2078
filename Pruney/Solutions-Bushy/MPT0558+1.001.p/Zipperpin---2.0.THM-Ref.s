%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0558+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dLyxO1tDoU

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:06 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 140 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          : 1685 (2784 expanded)
%              Number of equality atoms :   58 ( 104 expanded)
%              Maximal formula depth    :   24 (  12 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X10 ) @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

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

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( X17
       != ( k5_relat_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_F_1 @ X21 @ X18 @ X15 @ X16 ) ) @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X21 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('3',plain,(
    ! [X15: $i,X16: $i,X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X21 ) @ ( k5_relat_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_F_1 @ X21 @ X18 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('11',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X10 ) @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( X17
       != ( k5_relat_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X21 @ X18 @ X15 @ X16 ) @ X21 ) @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X21 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X21 ) @ ( k5_relat_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X21 @ X18 @ X15 @ X16 ) @ X21 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ X3 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('25',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X10 ) @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ X2 ) )
      | ( ( k9_relat_1 @ X1 @ X0 )
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('32',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X0 ) @ X1 ) @ X0 ) @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X5 ) @ X2 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X5 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ X2 ) )
      | ( ( k9_relat_1 @ X1 @ X0 )
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 @ X1 ) @ ( sk_C @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( X17
       != ( k5_relat_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X19 ) @ X15 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X19 ) @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k5_relat_1 @ X16 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ X2 )
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_C @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) @ X2 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) @ X2 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_C @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ( ( k9_relat_1 @ X0 @ X2 )
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X2 ) )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X0 ) @ X1 ) @ X0 ) @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X0 ) @ X1 ) @ X0 ) @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t160_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t160_relat_1])).

thf('59',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
     != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).


%------------------------------------------------------------------------------
