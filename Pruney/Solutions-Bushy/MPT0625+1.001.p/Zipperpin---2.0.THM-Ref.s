%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0625+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QrMofCEEbe

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:13 EST 2020

% Result     : Theorem 8.72s
% Output     : Refutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :  363 (8019 expanded)
%              Number of leaves         :   19 (2078 expanded)
%              Depth                    :   51
%              Number of atoms          : 7108 (207167 expanded)
%              Number of equality atoms :  386 (9863 expanded)
%              Maximal formula depth    :   24 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

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

thf('0',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_F @ X13 @ X11 @ X12 ) ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t20_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ! [D: $i] :
                      ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
                    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                        & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ ( k1_relat_1 @ B ) ) ) )
                  & ! [D: $i] :
                      ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
                     => ( ( k1_funct_1 @ C @ D )
                        = ( k1_funct_1 @ B @ ( k1_funct_1 @ A @ D ) ) ) ) )
               => ( C
                  = ( k5_relat_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ! [D: $i] :
                        ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
                      <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                          & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ ( k1_relat_1 @ B ) ) ) )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
                       => ( ( k1_funct_1 @ C @ D )
                          = ( k1_funct_1 @ B @ ( k1_funct_1 @ A @ D ) ) ) ) )
                 => ( C
                    = ( k5_relat_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_1])).

thf('6',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ( X3
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,(
    ! [X19: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X19 )
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) )
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) )
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('40',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ X21 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( r2_hidden @ X20 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X20 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( sk_C_1
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ X21 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_B )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_B )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X11: $i,X12: $i,X13: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ X18 ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X20: $i] :
      ( ( r2_hidden @ X20 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X20 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_F @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_F @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['95','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('121',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('126',plain,(
    ! [X19: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X19 )
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_F @ X13 @ X11 @ X12 ) ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('129',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_F @ X13 @ X11 @ X12 ) ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('130',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['131','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) @ X0 )
      | ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['148','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_C_1 )
      | ( X0
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_C_1 )
      | ( X0
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166'])).

thf('168',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['167','168'])).

thf('170',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('171',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ X21 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('174',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('179',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['169','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('182',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('183',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','183'])).

thf('185',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('186',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['184','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','183'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ( X1
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ( X1
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['200','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_C_1 )
      | ( X1
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_C_1 )
      | ( X1
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( sk_E @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( ( sk_E @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['199','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_E @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( ( sk_E @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['217','218','219','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( ( sk_E @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) @ X0 )
      | ( ( sk_F @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X11: $i,X12: $i,X13: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ X18 ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ X1 ) @ sk_A )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['198','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ sk_A ) @ ( sk_E @ sk_C_1 @ X0 @ sk_A ) ) @ X0 )
      | ( ( sk_F @ sk_C_1 @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['197','239'])).

thf('241',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['180','244'])).

thf('246',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','245'])).

thf('247',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('248',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('250',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['247','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( sk_E @ X2 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('255',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('256',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('257',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['254','258'])).

thf('260',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('262',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_F @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ X3 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_F @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_F @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_F @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['253','263'])).

thf('265',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_F @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('268',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X0 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) ) @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['265','269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( sk_E @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X2 @ ( sk_D_2 @ X2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X2 @ X1 @ X0 ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,(
    r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('273',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['274','275','276'])).

thf('278',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['271','277'])).

thf('279',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['278','279','280','281','282','283'])).

thf('285',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['284','285'])).

thf('287',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['177','178'])).

thf('288',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ X0 @ sk_A ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('290',plain,
    ( ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['284','285'])).

thf('291',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_F @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('292',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('293',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_F @ X0 @ X2 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf('294',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ X2 @ X1 ) ) ) @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_F @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_C_1 )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['290','294'])).

thf('296',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_C_1 )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['295','296','297','298','299','300'])).

thf('302',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['302','303'])).

thf('305',plain,(
    ! [X11: $i,X12: $i,X13: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ X18 ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('306',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['306','307','308','309'])).

thf('311',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['310','311'])).

thf('313',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['289','312'])).

thf('314',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['313','314'])).

thf('316',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['315','316'])).

thf('318',plain,
    ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['288','317'])).

thf('319',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['246','318'])).

thf('320',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['124','319'])).

thf('321',plain,(
    ! [X11: $i,X12: $i,X13: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X13 @ X11 @ X12 ) @ X18 ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('322',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['322','323','324','325'])).

thf('327',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['326','327'])).

thf('329',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_C_1
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','328'])).

thf('330',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( sk_F @ sk_C_1 @ sk_B @ sk_A )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['180','244'])).

thf('332',plain,(
    r2_hidden @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('333',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('334',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['332','333'])).

thf('335',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['334','335','336'])).

thf('338',plain,
    ( ( sk_E @ sk_C_1 @ sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['288','317'])).

thf('339',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_F @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['337','338'])).

thf('340',plain,
    ( sk_C_1
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['329','330','331','339'])).

thf('341',plain,(
    sk_C_1
 != ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['340','341'])).


%------------------------------------------------------------------------------
