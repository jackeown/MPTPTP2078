%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dKf3cCoKIM

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:14 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 292 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :   20
%              Number of atoms          : 1272 (4433 expanded)
%              Number of equality atoms :  171 ( 610 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t34_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( B
            = ( k6_relat_1 @ A ) )
        <=> ( ( ( k1_relat_1 @ B )
              = A )
            & ! [C: $i] :
                ( ( r2_hidden @ C @ A )
               => ( ( k1_funct_1 @ B @ C )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X15 )
        = X15 )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X15 )
          = X15 ) )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X15 )
          = X15 ) )
   <= ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X15 )
          = X15 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('19',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( ( sk_D @ sk_B @ sk_A )
        = ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( sk_D @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( ( sk_D @ sk_B @ sk_A )
        = ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( sk_D @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_D @ sk_B @ sk_A )
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('30',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

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

thf('32',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X8 ) @ X6 )
      | ( X8
       != ( k1_funct_1 @ X6 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( k1_funct_1 @ X6 @ X5 ) ) @ X6 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('40',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference('sup+',[status(thm)],['28','40'])).

thf('42',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( ( sk_C @ X0 @ X1 )
       != ( sk_D @ X0 @ X1 ) )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('44',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
       != ( sk_D @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
       != ( sk_D @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
       != ( sk_D @ sk_B @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('49',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
       != ( sk_D @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_D @ sk_B @ sk_A )
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('51',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_B
     != ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k6_relat_1 @ sk_A ) )
      & ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ~ ! [X15: $i] :
          ( ~ ( r2_hidden @ X15 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X15 )
            = X15 ) )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['52'])).

thf('60',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k1_relat_1 @ sk_B )
       != sk_A )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('63',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ X0 )
      | ( X2 != X4 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('66',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('67',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('72',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_C_1
        = ( k1_funct_1 @ sk_B @ sk_C_1 ) ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_B @ sk_C_1 ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 )
   <= ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('77',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
       != sk_C_1 )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
      = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','55','61','62','78'])).


%------------------------------------------------------------------------------
