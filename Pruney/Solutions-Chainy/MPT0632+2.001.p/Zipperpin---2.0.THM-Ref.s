%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.40gq89ANkF

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:49 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 260 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          : 1475 (4045 expanded)
%              Number of equality atoms :  191 ( 545 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X12: $i] :
      ( ~ ( r2_hidden @ X12 @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X12 )
        = X12 )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X12 )
          = X12 ) )
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
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
          = ( sk_D @ sk_B @ X0 ) )
        | ~ ( v1_funct_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ sk_A )
        | ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
          = ( sk_D @ sk_B @ X0 ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X12 )
          = X12 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X12 )
          = X12 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( ( sk_C @ sk_B @ X0 )
          = ( sk_D @ sk_B @ X0 ) )
        | ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ X0 ) )
          = ( sk_C @ sk_B @ X0 ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ( X11
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('19',plain,(
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
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D @ X0 @ X1 ) )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D @ sk_B @ X0 )
          = ( sk_C @ sk_B @ X0 ) )
        | ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
          = ( sk_D @ sk_B @ X0 ) )
        | ~ ( v1_relat_1 @ sk_B )
        | ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
          = ( sk_D @ sk_B @ X0 ) )
        | ~ ( v1_funct_1 @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D @ sk_B @ X0 )
          = ( sk_C @ sk_B @ X0 ) )
        | ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
          = ( sk_D @ sk_B @ X0 ) )
        | ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
          = ( sk_D @ sk_B @ X0 ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_D @ sk_B @ X0 )
          = ( sk_C @ sk_B @ X0 ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('38',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X12 )
          = X12 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ X12 )
          = X12 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( X11
       != ( k1_funct_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( k1_funct_1 @ X10 @ X9 ) ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference('sup+',[status(thm)],['39','51'])).

thf('53',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference('sup+',[status(thm)],['25','53'])).

thf('55',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( ( sk_C @ X0 @ X1 )
       != ( sk_D @ X0 @ X1 ) )
      | ( X0
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('57',plain,
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
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
       != ( sk_D @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
       != ( sk_D @ sk_B @ sk_A ) )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( sk_B
        = ( k6_relat_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('62',plain,
    ( ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
       != ( sk_D @ sk_B @ sk_A ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k6_relat_1 @ X0 ) )
        | ( ( sk_D @ sk_B @ X0 )
          = ( sk_C @ sk_B @ X0 ) ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('64',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_B
     != ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k6_relat_1 @ sk_A ) )
      & ( ( k1_relat_1 @ sk_B )
        = sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ~ ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ( ( k1_funct_1 @ sk_B @ X12 )
            = X12 ) )
    | ( sk_B
      = ( k6_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
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

thf('70',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['65'])).

thf('73',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k1_relat_1 @ sk_B )
       != sk_A )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['65'])).

thf('76',plain,
    ( ( sk_B
      = ( k6_relat_1 @ sk_A ) )
   <= ( sk_B
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ X0 )
      | ( X2 != X4 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('79',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('80',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('81',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_C_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ( X11
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('84',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C_1
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('86',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('87',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_B @ sk_C_1 ) )
   <= ( ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','87'])).

thf('89',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 )
   <= ( ( k1_funct_1 @ sk_B @ sk_C_1 )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['65'])).

thf('90',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
       != sk_C_1 )
      & ( sk_B
        = ( k6_relat_1 @ sk_A ) )
      & ( r2_hidden @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C_1 )
      = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A )
    | ( sk_B
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','68','74','75','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.40gq89ANkF
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 215 iterations in 0.105s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.37/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.56  thf(t34_funct_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.37/0.56         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i]:
% 0.37/0.56        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56          ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.37/0.56            ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t34_funct_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (((r2_hidden @ sk_C_1 @ sk_A)
% 0.37/0.56        | ((k1_relat_1 @ sk_B) != (sk_A))
% 0.37/0.56        | ((sk_B) != (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (((r2_hidden @ sk_C_1 @ sk_A)) | ~ (((sk_B) = (k6_relat_1 @ sk_A))) | 
% 0.37/0.56       ~ (((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A)) | ((sk_B) = (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) | (((sk_B) = (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X12 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56          | ((k1_funct_1 @ sk_B @ X12) = (X12))
% 0.37/0.56          | ((sk_B) = (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      ((![X12 : $i]:
% 0.37/0.56          (~ (r2_hidden @ X12 @ sk_A) | ((k1_funct_1 @ sk_B @ X12) = (X12)))) | 
% 0.37/0.56       (((sk_B) = (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['4'])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf(d10_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.37/0.56         ( ![C:$i,D:$i]:
% 0.37/0.56           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.37/0.56             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.37/0.56          | ((sk_C @ X0 @ X1) = (sk_D @ X0 @ X1))
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.37/0.56  thf(t8_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.56           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.37/0.56          | (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.37/0.56          | ~ (v1_funct_1 @ X10)
% 0.37/0.56          | ~ (v1_relat_1 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ((sk_C @ X0 @ X1) = (sk_D @ X0 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | ((sk_C @ X0 @ X1) = (sk_D @ X0 @ X1))
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r2_hidden @ (sk_C @ sk_B @ X0) @ sk_A)
% 0.37/0.56           | ~ (v1_relat_1 @ sk_B)
% 0.37/0.56           | ((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_C @ sk_B @ X0) = (sk_D @ sk_B @ X0))
% 0.37/0.56           | ~ (v1_funct_1 @ sk_B)))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['6', '10'])).
% 0.37/0.56  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((r2_hidden @ (sk_C @ sk_B @ X0) @ sk_A)
% 0.37/0.56           | ((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_C @ sk_B @ X0) = (sk_D @ sk_B @ X0))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      ((![X12 : $i]:
% 0.37/0.56          (~ (r2_hidden @ X12 @ sk_A) | ((k1_funct_1 @ sk_B @ X12) = (X12))))
% 0.37/0.56         <= ((![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('split', [status(esa)], ['4'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (((sk_C @ sk_B @ X0) = (sk_D @ sk_B @ X0))
% 0.37/0.56           | ((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ X0)) = (sk_C @ sk_B @ X0))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.37/0.56          | ((sk_C @ X0 @ X1) = (sk_D @ X0 @ X1))
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.37/0.56          | ((X11) = (k1_funct_1 @ X10 @ X9))
% 0.37/0.56          | ~ (v1_funct_1 @ X10)
% 0.37/0.56          | ~ (v1_relat_1 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ((sk_C @ X0 @ X1) = (sk_D @ X0 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1)))
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | ((sk_C @ X0 @ X1) = (sk_D @ X0 @ X1))
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (((sk_D @ sk_B @ X0) = (sk_C @ sk_B @ X0))
% 0.37/0.56           | ((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_C @ sk_B @ X0) = (sk_D @ sk_B @ X0))
% 0.37/0.56           | ~ (v1_relat_1 @ sk_B)
% 0.37/0.56           | ((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_C @ sk_B @ X0) = (sk_D @ sk_B @ X0))
% 0.37/0.56           | ~ (v1_funct_1 @ sk_B)))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['16', '20'])).
% 0.37/0.56  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (((sk_D @ sk_B @ X0) = (sk_C @ sk_B @ X0))
% 0.37/0.56           | ((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_C @ sk_B @ X0) = (sk_D @ sk_B @ X0))
% 0.37/0.56           | ((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_C @ sk_B @ X0) = (sk_D @ sk_B @ X0))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_D @ sk_B @ X0) = (sk_C @ sk_B @ X0))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.37/0.56          | (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.37/0.56          | ~ (v1_funct_1 @ X10)
% 0.37/0.56          | ~ (v1_relat_1 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_funct_1 @ X0))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.37/0.56         | ~ (v1_funct_1 @ sk_B)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.37/0.56         | ~ (v1_relat_1 @ sk_B))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['26', '31'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      ((((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      ((![X12 : $i]:
% 0.37/0.56          (~ (r2_hidden @ X12 @ sk_A) | ((k1_funct_1 @ sk_B @ X12) = (X12))))
% 0.37/0.56         <= ((![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('split', [status(esa)], ['4'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (((((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) = (sk_C @ sk_B @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_funct_1 @ X0))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['30'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.37/0.56          | ((X11) != (k1_funct_1 @ X10 @ X9))
% 0.37/0.56          | (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.37/0.56          | ~ (v1_funct_1 @ X10)
% 0.37/0.56          | ~ (v1_relat_1 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X10)
% 0.37/0.56          | ~ (v1_funct_1 @ X10)
% 0.37/0.56          | (r2_hidden @ (k4_tarski @ X9 @ (k1_funct_1 @ X10 @ X9)) @ X10)
% 0.37/0.56          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X10)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_funct_1 @ X0)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | (r2_hidden @ 
% 0.37/0.56             (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.37/0.56              (k1_funct_1 @ X0 @ (sk_C @ X0 @ (k1_relat_1 @ X0)))) @ 
% 0.37/0.56             X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ 
% 0.37/0.56           (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.37/0.56            (k1_funct_1 @ X0 @ (sk_C @ X0 @ (k1_relat_1 @ X0)))) @ 
% 0.37/0.56           X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.56          | ~ (v1_funct_1 @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      ((((r2_hidden @ 
% 0.37/0.56          (k4_tarski @ (sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56           (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))) @ 
% 0.37/0.56          sk_B)
% 0.37/0.56         | ~ (v1_funct_1 @ sk_B)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.37/0.56         | ~ (v1_relat_1 @ sk_B))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['40', '45'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      ((((r2_hidden @ 
% 0.37/0.56          (k4_tarski @ (sk_C @ sk_B @ sk_A) @ 
% 0.37/0.56           (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))) @ 
% 0.37/0.56          sk_B)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      ((((r2_hidden @ 
% 0.37/0.56          (k4_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ sk_B)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['39', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (((((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | (r2_hidden @ 
% 0.37/0.56            (k4_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ sk_B)))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      ((((r2_hidden @ 
% 0.37/0.56          (k4_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_D @ sk_B @ sk_A)) @ sk_B)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['25', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (((((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | (r2_hidden @ 
% 0.37/0.56            (k4_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_D @ sk_B @ sk_A)) @ sk_B)))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.37/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.37/0.56          | ((sk_C @ X0 @ X1) != (sk_D @ X0 @ X1))
% 0.37/0.56          | ((X0) = (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (((((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ~ (v1_relat_1 @ sk_B)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((sk_C @ sk_B @ sk_A) != (sk_D @ sk_B @ sk_A))
% 0.37/0.56         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.56  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (((((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((sk_C @ sk_B @ sk_A) != (sk_D @ sk_B @ sk_A))
% 0.37/0.56         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56         | ((sk_C @ sk_B @ sk_A) != (sk_D @ sk_B @ sk_A))
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['59'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      ((((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56         | ((sk_B) = (k6_relat_1 @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (((((sk_B) = (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((sk_C @ sk_B @ sk_A) != (sk_D @ sk_B @ sk_A))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('clc', [status(thm)], ['60', '61'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (((sk_B) = (k6_relat_1 @ X0))
% 0.37/0.56           | ((sk_D @ sk_B @ X0) = (sk_C @ sk_B @ X0))))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      ((((sk_B) = (k6_relat_1 @ sk_A)))
% 0.37/0.56         <= ((((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('clc', [status(thm)], ['62', '63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      ((((k1_funct_1 @ sk_B @ sk_C_1) != (sk_C_1))
% 0.37/0.56        | ((k1_relat_1 @ sk_B) != (sk_A))
% 0.37/0.56        | ((sk_B) != (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      ((((sk_B) != (k6_relat_1 @ sk_A)))
% 0.37/0.56         <= (~ (((sk_B) = (k6_relat_1 @ sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['65'])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      ((((sk_B) != (sk_B)))
% 0.37/0.56         <= (~ (((sk_B) = (k6_relat_1 @ sk_A))) & 
% 0.37/0.56             (((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (![X12 : $i]:
% 0.37/0.56                (~ (r2_hidden @ X12 @ sk_A)
% 0.37/0.56                 | ((k1_funct_1 @ sk_B @ X12) = (X12)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['64', '66'])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (~
% 0.37/0.56       (![X12 : $i]:
% 0.37/0.56          (~ (r2_hidden @ X12 @ sk_A) | ((k1_funct_1 @ sk_B @ X12) = (X12)))) | 
% 0.37/0.56       (((sk_B) = (k6_relat_1 @ sk_A))) | ~ (((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf(t71_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.37/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.56  thf('70', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['69', '70'])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) != (sk_A)))
% 0.37/0.56         <= (~ (((k1_relat_1 @ sk_B) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['65'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      ((((sk_A) != (sk_A)))
% 0.37/0.56         <= (~ (((k1_relat_1 @ sk_B) = (sk_A))) & 
% 0.37/0.56             (((sk_B) = (k6_relat_1 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_B) = (sk_A))) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['73'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      (~ (((k1_funct_1 @ sk_B @ sk_C_1) = (sk_C_1))) | 
% 0.37/0.56       ~ (((k1_relat_1 @ sk_B) = (sk_A))) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['65'])).
% 0.37/0.56  thf('76', plain,
% 0.37/0.56      ((((sk_B) = (k6_relat_1 @ sk_A))) <= ((((sk_B) = (k6_relat_1 @ sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['2'])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.56         (((X0) != (k6_relat_1 @ X1))
% 0.37/0.56          | (r2_hidden @ (k4_tarski @ X2 @ X4) @ X0)
% 0.37/0.56          | ((X2) != (X4))
% 0.37/0.56          | ~ (r2_hidden @ X2 @ X1)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.37/0.56  thf('79', plain,
% 0.37/0.56      (![X1 : $i, X4 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.37/0.56          | ~ (r2_hidden @ X4 @ X1)
% 0.37/0.56          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['78'])).
% 0.37/0.56  thf(fc3_funct_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.37/0.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.37/0.56  thf('80', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('81', plain,
% 0.37/0.56      (![X1 : $i, X4 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X4 @ X1)
% 0.37/0.56          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      (((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_C_1) @ (k6_relat_1 @ sk_A)))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['77', '81'])).
% 0.37/0.56  thf('83', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.37/0.56          | ((X11) = (k1_funct_1 @ X10 @ X9))
% 0.37/0.56          | ~ (v1_funct_1 @ X10)
% 0.37/0.56          | ~ (v1_relat_1 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.56  thf('84', plain,
% 0.37/0.56      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.37/0.56         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 0.37/0.56         | ((sk_C_1) = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ sk_C_1))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.56  thf('85', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('86', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('87', plain,
% 0.37/0.56      ((((sk_C_1) = (k1_funct_1 @ (k6_relat_1 @ sk_A) @ sk_C_1)))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.37/0.56  thf('88', plain,
% 0.37/0.56      ((((sk_C_1) = (k1_funct_1 @ sk_B @ sk_C_1)))
% 0.37/0.56         <= ((((sk_B) = (k6_relat_1 @ sk_A))) & ((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['76', '87'])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      ((((k1_funct_1 @ sk_B @ sk_C_1) != (sk_C_1)))
% 0.37/0.56         <= (~ (((k1_funct_1 @ sk_B @ sk_C_1) = (sk_C_1))))),
% 0.37/0.56      inference('split', [status(esa)], ['65'])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      ((((sk_C_1) != (sk_C_1)))
% 0.37/0.56         <= (~ (((k1_funct_1 @ sk_B @ sk_C_1) = (sk_C_1))) & 
% 0.37/0.56             (((sk_B) = (k6_relat_1 @ sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      ((((k1_funct_1 @ sk_B @ sk_C_1) = (sk_C_1))) | 
% 0.37/0.56       ~ ((r2_hidden @ sk_C_1 @ sk_A)) | ~ (((sk_B) = (k6_relat_1 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['90'])).
% 0.37/0.56  thf('92', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)],
% 0.37/0.56                ['1', '3', '5', '68', '74', '75', '91'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
