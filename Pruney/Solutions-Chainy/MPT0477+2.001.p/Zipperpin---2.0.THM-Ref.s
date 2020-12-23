%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5E7n8FVDVF

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 183 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  899 (2358 expanded)
%              Number of equality atoms :   56 ( 164 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t72_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t72_relat_1])).

thf('0',plain,(
    ( k4_relat_1 @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X5 @ X6 ) @ ( sk_C_1 @ X5 @ X6 ) ) @ X6 )
      | ( X5
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( sk_D_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X1 )
      | ( ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( sk_D_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X5 @ X6 ) @ ( sk_C_1 @ X5 @ X6 ) ) @ X6 )
      | ( X5
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ X0 )
      | ( X2 != X4 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('30',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X5 @ X6 ) @ ( sk_C_1 @ X5 @ X6 ) ) @ X6 )
      | ( X5
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) @ ( sk_C_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ( k6_relat_1 @ sk_A )
 != ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5E7n8FVDVF
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 100 iterations in 0.059s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.53  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.53  thf(t72_relat_1, conjecture,
% 0.20/0.53    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t72_relat_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((k4_relat_1 @ (k6_relat_1 @ sk_A)) != (k6_relat_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d7_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( v1_relat_1 @ B ) =>
% 0.20/0.53           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.20/0.53             ( ![C:$i,D:$i]:
% 0.20/0.53               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.53                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X5)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D_1 @ X5 @ X6)) @ X5)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_D_1 @ X5 @ X6) @ (sk_C_1 @ X5 @ X6)) @ X6)
% 0.20/0.53          | ((X5) = (k4_relat_1 @ X6))
% 0.20/0.53          | ~ (v1_relat_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.20/0.53  thf(d10_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.53         ( ![C:$i,D:$i]:
% 0.20/0.53           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.53             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (((X0) != (k6_relat_1 @ X1))
% 0.20/0.53          | ((X2) = (X3))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.20/0.53          | ((X2) = (X3)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.53  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.53  thf('4', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.20/0.53          | ((X2) = (X3)))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ((k6_relat_1 @ X0) = (k4_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_D_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.20/0.53             X1)
% 0.20/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.53          | ((sk_C_1 @ (k6_relat_1 @ X0) @ X1)
% 0.20/0.53              = (sk_D_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.53  thf('7', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ((k6_relat_1 @ X0) = (k4_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_D_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.20/0.53             X1)
% 0.20/0.53          | ((sk_C_1 @ (k6_relat_1 @ X0) @ X1)
% 0.20/0.53              = (sk_D_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.20/0.53          | ((X2) = (X3)))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.20/0.53            = (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.53          | ((sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.20/0.53              = (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.20/0.53            = (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.20/0.53              = (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.20/0.53              = (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X5)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D_1 @ X5 @ X6)) @ X5)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_D_1 @ X5 @ X6) @ (sk_C_1 @ X5 @ X6)) @ X6)
% 0.20/0.53          | ((X5) = (k4_relat_1 @ X6))
% 0.20/0.53          | ~ (v1_relat_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (((X0) != (k6_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ X2 @ X1)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ X2 @ X1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf('17', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ X2 @ X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ((k6_relat_1 @ X0) = (k4_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_D_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.20/0.53             X1)
% 0.20/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '18'])).
% 0.20/0.53  thf('20', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | ((k6_relat_1 @ X0) = (k4_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_D_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.20/0.53             X1)
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ X2 @ X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X1)
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.53          | (r2_hidden @ (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X1)
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | (r2_hidden @ (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X0)
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['13', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X1)
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)) @ X0)
% 0.20/0.53          | ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.53         (((X0) != (k6_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X2 @ X4) @ X0)
% 0.20/0.53          | ((X2) != (X4))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X1 : $i, X4 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X4 @ X1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.53  thf('31', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X1 : $i, X4 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X4 @ X1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.20/0.53              = (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.20/0.53              = (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X5)
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D_1 @ X5 @ X6)) @ X5)
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_D_1 @ X5 @ X6) @ (sk_C_1 @ X5 @ X6)) @ X6)
% 0.20/0.53          | ((X5) = (k4_relat_1 @ X6))
% 0.20/0.53          | ~ (v1_relat_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X1))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53                (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53               (k6_relat_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('39', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X1))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53                (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53               (k6_relat_1 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_D_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X0))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53                (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53               (k6_relat_1 @ X1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X0))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53                (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53               (k6_relat_1 @ X1))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X1))
% 0.20/0.53          | ((k6_relat_1 @ X1) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53                (sk_C_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53               (k6_relat_1 @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ 
% 0.20/0.53               (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53                (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53               (k6_relat_1 @ X0))
% 0.20/0.53          | ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X0))
% 0.20/0.53          | ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)) @ 
% 0.20/0.53              (sk_C_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))) @ 
% 0.20/0.53             (k6_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '32'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.53      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain, (((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '47'])).
% 0.20/0.53  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
