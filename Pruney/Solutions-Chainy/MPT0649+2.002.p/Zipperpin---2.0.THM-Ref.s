%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OOpfr24zQJ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 285 expanded)
%              Number of leaves         :   20 (  89 expanded)
%              Depth                    :   24
%              Number of atoms          :  990 (4125 expanded)
%              Number of equality atoms :   44 ( 254 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('6',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

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

thf('9',plain,(
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

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( X16
       != ( k1_funct_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( k1_funct_1 @ X15 @ X14 ) ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

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

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X8 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

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

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k1_funct_1 @ X12 @ ( k1_funct_1 @ X11 @ X13 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('52',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ( X16
        = ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['49','62','63','64'])).

thf('66',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('67',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('75',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('76',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('77',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('85',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['73','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['91','92','93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OOpfr24zQJ
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:58:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 95 iterations in 0.085s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(d9_funct_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.54       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X6 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X6)
% 0.20/0.54          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.20/0.54          | ~ (v1_funct_1 @ X6)
% 0.20/0.54          | ~ (v1_relat_1 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.54  thf(dt_k2_funct_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X7 : $i]:
% 0.20/0.54         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.20/0.54          | ~ (v1_funct_1 @ X7)
% 0.20/0.54          | ~ (v1_relat_1 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ~ (v2_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf(dt_k4_relat_1, axiom,
% 0.20/0.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.54  thf(t56_funct_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.54         ( ( ( A ) =
% 0.20/0.54             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.20/0.54           ( ( A ) =
% 0.20/0.54             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.54            ( ( ( A ) =
% 0.20/0.54                ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.20/0.54              ( ( A ) =
% 0.20/0.54                ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t56_funct_1])).
% 0.20/0.54  thf('9', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t8_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.54           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.20/0.54          | ((X16) != (k1_funct_1 @ X15 @ X14))
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.20/0.54          | ~ (v1_funct_1 @ X15)
% 0.20/0.54          | ~ (v1_relat_1 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X15)
% 0.20/0.54          | ~ (v1_funct_1 @ X15)
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X14 @ (k1_funct_1 @ X15 @ X14)) @ X15)
% 0.20/0.54          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X15)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.54  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.54  thf(d7_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( v1_relat_1 @ B ) =>
% 0.20/0.54           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.20/0.54             ( ![C:$i,D:$i]:
% 0.20/0.54               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.54                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X0)
% 0.20/0.54          | ((X0) != (k4_relat_1 @ X1))
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.20/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.20/0.54          | ~ (v1_relat_1 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X1)
% 0.20/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k4_relat_1 @ X1))
% 0.20/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X0)
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.20/0.54          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | (r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.54           (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '20'])).
% 0.20/0.54  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.54        (k4_relat_1 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.20/0.54          | (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.20/0.54          | ~ (v1_funct_1 @ X15)
% 0.20/0.54          | ~ (v1_relat_1 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.54           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.54           (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '25'])).
% 0.20/0.54  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.54         (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.54        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.54           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '28'])).
% 0.20/0.54  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('32', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.54        (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.54  thf(t21_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.20/0.54             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.54               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X8)
% 0.20/0.54          | ~ (v1_funct_1 @ X8)
% 0.20/0.54          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.20/0.54          | ~ (r2_hidden @ (k1_funct_1 @ X8 @ X9) @ (k1_relat_1 @ X10))
% 0.20/0.54          | (r2_hidden @ X9 @ (k1_relat_1 @ (k5_relat_1 @ X8 @ X10)))
% 0.20/0.54          | ~ (v1_funct_1 @ X10)
% 0.20/0.54          | ~ (v1_relat_1 @ X10))),
% 0.20/0.54      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | (r2_hidden @ sk_A @ 
% 0.20/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))
% 0.20/0.54        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('36', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | (r2_hidden @ sk_A @ 
% 0.20/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)))))),
% 0.20/0.54      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | (r2_hidden @ sk_A @ 
% 0.20/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '39'])).
% 0.20/0.54  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ 
% 0.20/0.54         (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.54        | (r2_hidden @ sk_A @ 
% 0.20/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '42'])).
% 0.20/0.54  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      ((r2_hidden @ sk_A @ 
% 0.20/0.54        (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.20/0.54  thf(t22_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.20/0.54             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.20/0.54               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X11)
% 0.20/0.54          | ~ (v1_funct_1 @ X11)
% 0.20/0.54          | ((k1_funct_1 @ (k5_relat_1 @ X11 @ X12) @ X13)
% 0.20/0.54              = (k1_funct_1 @ X12 @ (k1_funct_1 @ X11 @ X13)))
% 0.20/0.54          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X12)))
% 0.20/0.54          | ~ (v1_funct_1 @ X12)
% 0.20/0.54          | ~ (v1_relat_1 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A)
% 0.20/0.54            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.54        (k4_relat_1 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.20/0.54          | ((X16) = (k1_funct_1 @ X15 @ X14))
% 0.20/0.54          | ~ (v1_funct_1 @ X15)
% 0.20/0.54          | ~ (v1_relat_1 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ((sk_A)
% 0.20/0.54            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | ((sk_A)
% 0.20/0.54            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '54'])).
% 0.20/0.54  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((((sk_A)
% 0.20/0.54          = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.54        | ((sk_A)
% 0.20/0.54            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '57'])).
% 0.20/0.54  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('61', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (((sk_A)
% 0.20/0.54         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.20/0.54  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A)
% 0.20/0.54            = (sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['49', '62', '63', '64'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (![X6 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X6)
% 0.20/0.54          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.20/0.54          | ~ (v1_funct_1 @ X6)
% 0.20/0.54          | ~ (v1_relat_1 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      ((((sk_A)
% 0.20/0.54          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.54        | ((sk_A)
% 0.20/0.54            != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      ((((sk_A)
% 0.20/0.54          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((sk_A)
% 0.20/0.54                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.20/0.54                   sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (((((sk_A)
% 0.20/0.54           != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A))
% 0.20/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54         | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54         | ~ (v2_funct_1 @ sk_B)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((sk_A)
% 0.20/0.54                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.20/0.54                   sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['66', '68'])).
% 0.20/0.54  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('72', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      ((((sk_A)
% 0.20/0.54          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((sk_A)
% 0.20/0.54                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.20/0.54                   sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (((sk_A)
% 0.20/0.54         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (![X6 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ X6)
% 0.20/0.54          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.20/0.54          | ~ (v1_funct_1 @ X6)
% 0.20/0.54          | ~ (v1_relat_1 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      ((((sk_A)
% 0.20/0.54          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.20/0.54         <= (~
% 0.20/0.54             (((sk_A)
% 0.20/0.54                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.20/0.54                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.20/0.54      inference('split', [status(esa)], ['67'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      (((((sk_A)
% 0.20/0.54           != (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54         | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54         | ~ (v2_funct_1 @ sk_B)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((sk_A)
% 0.20/0.54                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.20/0.54                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.54  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('80', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      ((((sk_A)
% 0.20/0.54          != (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.20/0.54         <= (~
% 0.20/0.54             (((sk_A)
% 0.20/0.54                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.20/0.54                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.20/0.54      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      ((((sk_A) != (sk_A)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((sk_A)
% 0.20/0.54                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.20/0.54                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['74', '81'])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      ((((sk_A)
% 0.20/0.54          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['82'])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((sk_A)
% 0.20/0.54          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))) | 
% 0.20/0.54       ~
% 0.20/0.54       (((sk_A)
% 0.20/0.54          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['67'])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((sk_A)
% 0.20/0.54          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.20/0.54  thf('86', plain,
% 0.20/0.54      (((sk_A)
% 0.20/0.54         != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['73', '85'])).
% 0.20/0.54  thf('87', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.20/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['65', '86'])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '87'])).
% 0.20/0.54  thf('89', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('90', plain, (~ (v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '90'])).
% 0.20/0.54  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('93', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('94', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('95', plain, ($false),
% 0.20/0.54      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
