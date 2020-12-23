%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0622+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TjN7dB28zN

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 142 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  506 (2193 expanded)
%              Number of equality atoms :   55 ( 306 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t17_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = ( k1_relat_1 @ C ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_tarski @ A ) )
              & ( ( k2_relat_1 @ C )
                = ( k1_tarski @ A ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = ( k1_relat_1 @ C ) )
                & ( ( k2_relat_1 @ B )
                  = ( k1_tarski @ A ) )
                & ( ( k2_relat_1 @ C )
                  = ( k1_tarski @ A ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_C_3 ) )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_C_3 = sk_B )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C_3 = sk_B )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    sk_B != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( X10
       != ( k1_funct_1 @ X6 @ X11 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('15',plain,(
    ! [X6: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X11 ) @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','19','20','21'])).

thf('23',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_B @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_B @ sk_C_3 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( ( k1_funct_1 @ X13 @ ( sk_C_2 @ X12 @ X13 ) )
       != ( k1_funct_1 @ X12 @ ( sk_C_2 @ X12 @ X13 ) ) )
      | ( ( k1_relat_1 @ X13 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('30',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_C_2 @ sk_B @ sk_C_3 ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_3 = sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_C_2 @ sk_B @ sk_C_3 ) ) )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( sk_C_3 = sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35'])).

thf('37',plain,
    ( ( sk_C_3 = sk_B )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_C_2 @ sk_B @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_B != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_A
 != ( k1_funct_1 @ sk_B @ ( sk_C_2 @ sk_B @ sk_C_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('41',plain,(
    ! [X6: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X11 ) @ ( k2_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('42',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_2 @ sk_B @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_2 @ sk_B @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('47',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C_2 @ sk_B @ sk_C_3 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['39','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).


%------------------------------------------------------------------------------
