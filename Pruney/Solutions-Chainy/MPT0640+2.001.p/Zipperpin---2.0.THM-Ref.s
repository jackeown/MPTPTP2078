%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3AXle3c1jt

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 214 expanded)
%              Number of leaves         :   19 (  72 expanded)
%              Depth                    :   25
%              Number of atoms          :  924 (2946 expanded)
%              Number of equality atoms :   54 (  79 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t47_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
                & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
             => ( v2_funct_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('2',plain,(
    ! [X4: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_B @ X4 ) )
        = ( k1_funct_1 @ X4 @ ( sk_C @ X4 ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('4',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

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

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X9 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('24',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('34',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X4 ) )
      | ( ( k1_funct_1 @ X4 @ X5 )
       != ( k1_funct_1 @ X4 @ X6 ) )
      | ( X5 = X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('38',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_B @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_B @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( sk_B @ sk_B_1 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
       != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
    | ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','54'])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
    | ( v2_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_C @ sk_B_1 )
    = ( sk_B @ sk_B_1 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( ( sk_B @ X4 )
       != ( sk_C @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('70',plain,
    ( ( ( sk_B @ sk_B_1 )
     != ( sk_B @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( sk_B @ sk_B_1 )
     != ( sk_B @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3AXle3c1jt
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 38 iterations in 0.029s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(t47_funct_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.21/0.49               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.49             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49              ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.21/0.49                  ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.49                ( v2_funct_1 @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t47_funct_1])).
% 0.21/0.49  thf('0', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d8_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.49         ( ![B:$i,C:$i]:
% 0.21/0.49           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.49               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.49               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.49             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ X4) @ (k1_relat_1 @ X4))
% 0.21/0.49          | (v2_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (((k1_funct_1 @ X4 @ (sk_B @ X4)) = (k1_funct_1 @ X4 @ (sk_C @ X4)))
% 0.21/0.49          | (v2_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ X4) @ (k1_relat_1 @ X4))
% 0.21/0.49          | (v2_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('4', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t46_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X2)
% 0.21/0.49          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2)) = (k1_relat_1 @ X3))
% 0.21/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X3) @ (k1_relat_1 @ X2))
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49        | ((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.49  thf(t22_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.49             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.21/0.49               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X9 @ X10) @ X11)
% 0.21/0.49              = (k1_funct_1 @ X10 @ (k1_funct_1 @ X9 @ X11)))
% 0.21/0.49          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X10)))
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0)))
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49          | ~ (v1_relat_1 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ (sk_C @ sk_B_1))
% 0.21/0.49            = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '16'])).
% 0.21/0.49  thf('18', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ (sk_C @ sk_B_1))
% 0.21/0.49            = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1)))))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.49  thf('21', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ (sk_C @ sk_B_1))
% 0.21/0.49         = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1))))),
% 0.21/0.49      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ X4) @ (k1_relat_1 @ X4))
% 0.21/0.49          | (v2_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ X4) @ (k1_relat_1 @ X4))
% 0.21/0.49          | (v2_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.49            = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.49            = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.49  thf('30', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.49         = (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 0.21/0.49      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf(fc2_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.21/0.49         ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.21/0.49         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v1_relat_1 @ X8)
% 0.21/0.49          | ~ (v1_funct_1 @ X8)
% 0.21/0.49          | (v1_funct_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.21/0.49  thf(dt_k5_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.49       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X1)
% 0.21/0.49          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X4)
% 0.21/0.49          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.21/0.49          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X4))
% 0.21/0.49          | ((k1_funct_1 @ X4 @ X5) != (k1_funct_1 @ X4 @ X6))
% 0.21/0.49          | ((X5) = (X6))
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.21/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))
% 0.21/0.49          | ~ (v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((k1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.49  thf('38', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.21/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ sk_A)
% 0.21/0.49          | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.21/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '39'])).
% 0.21/0.49  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1)
% 0.21/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ sk_A)
% 0.21/0.49          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.49          | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '43'])).
% 0.21/0.49  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              != (k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49            != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.21/0.49          | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((X0) = (sk_B @ sk_B_1))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49          | (v2_funct_1 @ sk_B_1)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((X0) = (sk_B @ sk_B_1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '50'])).
% 0.21/0.49  thf('52', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_funct_1 @ sk_B_1)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49          | ((X0) = (sk_B @ sk_B_1))
% 0.21/0.49          | ((k1_funct_1 @ (k5_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.21/0.49              != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 0.21/0.49      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1)))
% 0.21/0.49          != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.21/0.49        | ((sk_C @ sk_B_1) = (sk_B @ sk_B_1))
% 0.21/0.49        | ~ (r2_hidden @ (sk_C @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49        | (v2_funct_1 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.49          != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ~ (r2_hidden @ (sk_C @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49        | ((sk_C @ sk_B_1) = (sk_B @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '55'])).
% 0.21/0.49  thf('57', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('58', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.49          != (k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 0.21/0.49        | (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ~ (r2_hidden @ (sk_C @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49        | ((sk_C @ sk_B_1) = (sk_B @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((((sk_C @ sk_B_1) = (sk_B @ sk_B_1))
% 0.21/0.49        | ~ (r2_hidden @ (sk_C @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49        | (v2_funct_1 @ sk_B_1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.49  thf('61', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      ((~ (r2_hidden @ (sk_C @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49        | ((sk_C @ sk_B_1) = (sk_B @ sk_B_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ((sk_C @ sk_B_1) = (sk_B @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '62'])).
% 0.21/0.49  thf('64', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (((v2_funct_1 @ sk_B_1) | ((sk_C @ sk_B_1) = (sk_B @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.49  thf('67', plain, (~ (v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain, (((sk_C @ sk_B_1) = (sk_B @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (((sk_B @ X4) != (sk_C @ X4))
% 0.21/0.49          | (v2_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      ((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | (v2_funct_1 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('72', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.21/0.49  thf('74', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.49  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
