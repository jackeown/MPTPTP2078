%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LJ1OZHDcwq

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 200 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   22
%              Number of atoms          :  758 (2854 expanded)
%              Number of equality atoms :   46 ( 191 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t56_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_funct_1])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k1_funct_1 @ X8 @ ( k1_funct_1 @ X9 @ X10 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('12',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( X13
       != ( k1_funct_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( k1_funct_1 @ X12 @ X11 ) ) @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

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

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X12 )
      | ( X13
        = ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('47',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('48',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('56',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['18','56'])).

thf('58',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','57'])).

thf('59',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('60',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LJ1OZHDcwq
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:56:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 58 iterations in 0.034s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.45  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.45  thf(dt_k4_relat_1, axiom,
% 0.19/0.45    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.19/0.45  thf(d9_funct_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.45       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X6 : $i]:
% 0.19/0.45         (~ (v2_funct_1 @ X6)
% 0.19/0.45          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.19/0.45          | ~ (v1_funct_1 @ X6)
% 0.19/0.45          | ~ (v1_relat_1 @ X6))),
% 0.19/0.45      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.19/0.45  thf(dt_k2_funct_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.19/0.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X7 : $i]:
% 0.19/0.45         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.19/0.45          | ~ (v1_funct_1 @ X7)
% 0.19/0.45          | ~ (v1_relat_1 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_funct_1 @ X0)
% 0.19/0.45          | ~ (v2_funct_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | ~ (v1_funct_1 @ X0))),
% 0.19/0.45      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (v2_funct_1 @ X0)
% 0.19/0.45          | ~ (v1_funct_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.45  thf(t56_funct_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.45       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.19/0.45         ( ( ( A ) =
% 0.19/0.45             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.19/0.45           ( ( A ) =
% 0.19/0.45             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.45          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.19/0.45            ( ( ( A ) =
% 0.19/0.45                ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.19/0.45              ( ( A ) =
% 0.19/0.45                ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t56_funct_1])).
% 0.19/0.45  thf('5', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t23_funct_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.45       ( ![C:$i]:
% 0.19/0.45         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.45           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.45             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.19/0.45               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X8)
% 0.19/0.45          | ~ (v1_funct_1 @ X8)
% 0.19/0.45          | ((k1_funct_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.19/0.45              = (k1_funct_1 @ X8 @ (k1_funct_1 @ X9 @ X10)))
% 0.19/0.45          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.19/0.45          | ~ (v1_funct_1 @ X9)
% 0.19/0.45          | ~ (v1_relat_1 @ X9))),
% 0.19/0.45      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ sk_B)
% 0.19/0.45          | ~ (v1_funct_1 @ sk_B)
% 0.19/0.45          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ sk_A)
% 0.19/0.45              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.45          | ~ (v1_funct_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ sk_A)
% 0.19/0.45            = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.45          | ~ (v1_funct_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X6 : $i]:
% 0.19/0.45         (~ (v2_funct_1 @ X6)
% 0.19/0.45          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.19/0.45          | ~ (v1_funct_1 @ X6)
% 0.19/0.45          | ~ (v1_relat_1 @ X6))),
% 0.19/0.45      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.45        | ((sk_A)
% 0.19/0.45            != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((sk_A)
% 0.19/0.45                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.19/0.45                   sk_A))))),
% 0.19/0.45      inference('split', [status(esa)], ['12'])).
% 0.19/0.45  thf('14', plain,
% 0.19/0.45      (((((sk_A)
% 0.19/0.45           != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A))
% 0.19/0.45         | ~ (v1_relat_1 @ sk_B)
% 0.19/0.45         | ~ (v1_funct_1 @ sk_B)
% 0.19/0.45         | ~ (v2_funct_1 @ sk_B)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((sk_A)
% 0.19/0.45                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.19/0.45                   sk_A))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['11', '13'])).
% 0.19/0.45  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('17', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('18', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((sk_A)
% 0.19/0.45                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.19/0.45                   sk_A))))),
% 0.19/0.45      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.19/0.45  thf('19', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (v2_funct_1 @ X0)
% 0.19/0.45          | ~ (v1_funct_1 @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0)
% 0.19/0.45          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.45  thf('20', plain,
% 0.19/0.45      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.19/0.45  thf('21', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t8_funct_1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.45       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.45         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.19/0.45           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.19/0.45  thf('22', plain,
% 0.19/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.19/0.45          | ((X13) != (k1_funct_1 @ X12 @ X11))
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X11 @ X13) @ X12)
% 0.19/0.45          | ~ (v1_funct_1 @ X12)
% 0.19/0.45          | ~ (v1_relat_1 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.19/0.45  thf('23', plain,
% 0.19/0.45      (![X11 : $i, X12 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X12)
% 0.19/0.45          | ~ (v1_funct_1 @ X12)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X11 @ (k1_funct_1 @ X12 @ X11)) @ X12)
% 0.19/0.45          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.45  thf('24', plain,
% 0.19/0.45      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.19/0.45        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.45        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.45      inference('sup-', [status(thm)], ['21', '23'])).
% 0.19/0.45  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('27', plain,
% 0.19/0.45      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.19/0.45      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.19/0.45  thf('28', plain,
% 0.19/0.45      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.19/0.45  thf(d7_relat_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ A ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( v1_relat_1 @ B ) =>
% 0.19/0.45           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.19/0.45             ( ![C:$i,D:$i]:
% 0.19/0.45               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.19/0.45                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.19/0.45  thf('29', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X0)
% 0.19/0.45          | ((X0) != (k4_relat_1 @ X1))
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.19/0.45          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.19/0.45          | ~ (v1_relat_1 @ X1))),
% 0.19/0.45      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.19/0.45  thf('30', plain,
% 0.19/0.45      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X1)
% 0.19/0.45          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k4_relat_1 @ X1))
% 0.19/0.45          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.45  thf('31', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X0)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.19/0.45          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['28', '30'])).
% 0.19/0.45  thf('32', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.19/0.45          | ~ (v1_relat_1 @ X0))),
% 0.19/0.45      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.45  thf('33', plain,
% 0.19/0.45      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.45        | (r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.19/0.45           (k4_relat_1 @ sk_B)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['27', '32'])).
% 0.19/0.45  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('35', plain,
% 0.19/0.45      ((r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.19/0.45        (k4_relat_1 @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.45  thf('36', plain,
% 0.19/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.45         (~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ X12)
% 0.19/0.45          | ((X13) = (k1_funct_1 @ X12 @ X11))
% 0.19/0.45          | ~ (v1_funct_1 @ X12)
% 0.19/0.45          | ~ (v1_relat_1 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.19/0.45  thf('37', plain,
% 0.19/0.45      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.19/0.45        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.19/0.45        | ((sk_A)
% 0.19/0.45            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.45  thf('38', plain,
% 0.19/0.45      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.45        | ((sk_A)
% 0.19/0.45            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.45        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['20', '37'])).
% 0.19/0.45  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('40', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.45        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.19/0.45      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.45  thf('41', plain,
% 0.19/0.45      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.45        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.45        | ~ (v2_funct_1 @ sk_B)
% 0.19/0.45        | ((sk_A)
% 0.19/0.45            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['19', '40'])).
% 0.19/0.45  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('44', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('45', plain,
% 0.19/0.45      (((sk_A)
% 0.19/0.45         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.45      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.19/0.45  thf('46', plain,
% 0.19/0.45      (![X6 : $i]:
% 0.19/0.45         (~ (v2_funct_1 @ X6)
% 0.19/0.45          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.19/0.45          | ~ (v1_funct_1 @ X6)
% 0.19/0.45          | ~ (v1_relat_1 @ X6))),
% 0.19/0.45      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.19/0.45  thf('47', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.19/0.45         <= (~
% 0.19/0.45             (((sk_A)
% 0.19/0.45                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.45                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.19/0.45      inference('split', [status(esa)], ['12'])).
% 0.19/0.45  thf('48', plain,
% 0.19/0.45      (((((sk_A)
% 0.19/0.45           != (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.45         | ~ (v1_relat_1 @ sk_B)
% 0.19/0.45         | ~ (v1_funct_1 @ sk_B)
% 0.19/0.45         | ~ (v2_funct_1 @ sk_B)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((sk_A)
% 0.19/0.45                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.45                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.45  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('51', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('52', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          != (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.19/0.45         <= (~
% 0.19/0.45             (((sk_A)
% 0.19/0.45                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.45                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.19/0.45      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.19/0.45  thf('53', plain,
% 0.19/0.45      ((((sk_A) != (sk_A)))
% 0.19/0.45         <= (~
% 0.19/0.45             (((sk_A)
% 0.19/0.45                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.19/0.45                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.19/0.45      inference('sup-', [status(thm)], ['45', '52'])).
% 0.19/0.45  thf('54', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.19/0.45      inference('simplify', [status(thm)], ['53'])).
% 0.19/0.45  thf('55', plain,
% 0.19/0.45      (~
% 0.19/0.45       (((sk_A)
% 0.19/0.45          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))) | 
% 0.19/0.45       ~
% 0.19/0.45       (((sk_A)
% 0.19/0.45          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.19/0.45      inference('split', [status(esa)], ['12'])).
% 0.19/0.45  thf('56', plain,
% 0.19/0.45      (~
% 0.19/0.45       (((sk_A)
% 0.19/0.45          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.19/0.45      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.19/0.45  thf('57', plain,
% 0.19/0.45      (((sk_A)
% 0.19/0.45         != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A))),
% 0.19/0.45      inference('simpl_trail', [status(thm)], ['18', '56'])).
% 0.19/0.45  thf('58', plain,
% 0.19/0.45      ((((sk_A)
% 0.19/0.45          != (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.19/0.45        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.19/0.45        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['10', '57'])).
% 0.19/0.45  thf('59', plain,
% 0.19/0.45      (((sk_A)
% 0.19/0.45         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.19/0.45      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.19/0.45  thf('60', plain,
% 0.19/0.45      ((((sk_A) != (sk_A))
% 0.19/0.45        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.19/0.45        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.19/0.45      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.45  thf('61', plain,
% 0.19/0.45      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.19/0.45        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['60'])).
% 0.19/0.45  thf('62', plain,
% 0.19/0.45      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.45        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.45        | ~ (v2_funct_1 @ sk_B)
% 0.19/0.45        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '61'])).
% 0.19/0.45  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('66', plain, (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.19/0.45  thf('67', plain, (~ (v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('sup-', [status(thm)], ['0', '66'])).
% 0.19/0.45  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('69', plain, ($false), inference('demod', [status(thm)], ['67', '68'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
