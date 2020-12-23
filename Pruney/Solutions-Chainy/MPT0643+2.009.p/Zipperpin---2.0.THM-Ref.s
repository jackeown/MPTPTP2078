%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAmcWv9Irf

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 189 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  730 (3424 expanded)
%              Number of equality atoms :   65 ( 412 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t50_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = A )
                & ( ( k1_relat_1 @ C )
                  = A )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( v2_funct_1 @ B )
                & ( ( k5_relat_1 @ C @ B )
                  = B ) )
             => ( C
                = ( k6_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
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

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != X10 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 )
      | ( X11
        = ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A )
    | ( sk_C_2
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    sk_C_2
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k5_relat_1 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) @ X9 )
        = ( k1_funct_1 @ X8 @ ( k1_funct_1 @ X7 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_2 @ sk_B_1 ) @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k5_relat_1 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17','18','19'])).

thf('21',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
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

thf('23',plain,(
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

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ( ( k8_relat_1 @ X3 @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k8_relat_1 @ sk_A @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k8_relat_1 @ sk_A @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t40_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X2 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['30','46'])).

thf('48',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
      = ( sk_C_1 @ sk_C_2 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
    = ( sk_C_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != X10 )
      | ( ( k1_funct_1 @ X11 @ ( sk_C_1 @ X11 @ X10 ) )
       != ( sk_C_1 @ X11 @ X10 ) )
      | ( X11
        = ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('53',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) )
       != ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
     != ( sk_C_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ( sk_C_2
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
     != ( sk_C_1 @ sk_C_2 @ sk_A ) )
    | ( sk_C_2
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    sk_C_2
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
 != ( sk_C_1 @ sk_C_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAmcWv9Irf
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.57  % Solved by: fo/fo7.sh
% 0.19/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.57  % done 279 iterations in 0.130s
% 0.19/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.57  % SZS output start Refutation
% 0.19/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.57  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.57  thf(t50_funct_1, conjecture,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.57       ( ![C:$i]:
% 0.19/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.57           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.57               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.19/0.57               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 0.19/0.57               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.19/0.57             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.57    (~( ![A:$i,B:$i]:
% 0.19/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.57          ( ![C:$i]:
% 0.19/0.57            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.57              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.57                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.19/0.57                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.19/0.57                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.19/0.57                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 0.19/0.57    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 0.19/0.57  thf('0', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(t34_funct_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.57       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.19/0.57         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.57           ( ![C:$i]:
% 0.19/0.57             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.19/0.57  thf('1', plain,
% 0.19/0.57      (![X10 : $i, X11 : $i]:
% 0.19/0.57         (((k1_relat_1 @ X11) != (X10))
% 0.19/0.57          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10)
% 0.19/0.57          | ((X11) = (k6_relat_1 @ X10))
% 0.19/0.57          | ~ (v1_funct_1 @ X11)
% 0.19/0.57          | ~ (v1_relat_1 @ X11))),
% 0.19/0.57      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.19/0.57  thf('2', plain,
% 0.19/0.57      (![X11 : $i]:
% 0.19/0.57         (~ (v1_relat_1 @ X11)
% 0.19/0.57          | ~ (v1_funct_1 @ X11)
% 0.19/0.57          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.19/0.57          | (r2_hidden @ (sk_C_1 @ X11 @ (k1_relat_1 @ X11)) @ 
% 0.19/0.57             (k1_relat_1 @ X11)))),
% 0.19/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.57  thf('3', plain,
% 0.19/0.57      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ (k1_relat_1 @ sk_C_2))
% 0.19/0.57        | ((sk_C_2) = (k6_relat_1 @ (k1_relat_1 @ sk_C_2)))
% 0.19/0.57        | ~ (v1_funct_1 @ sk_C_2)
% 0.19/0.57        | ~ (v1_relat_1 @ sk_C_2))),
% 0.19/0.57      inference('sup+', [status(thm)], ['0', '2'])).
% 0.19/0.57  thf('4', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('5', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('6', plain, ((v1_funct_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('7', plain, ((v1_relat_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('8', plain,
% 0.19/0.57      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A)
% 0.19/0.57        | ((sk_C_2) = (k6_relat_1 @ sk_A)))),
% 0.19/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.19/0.57  thf('9', plain, (((sk_C_2) != (k6_relat_1 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('10', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A)),
% 0.19/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.57  thf('11', plain, (((k5_relat_1 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(t22_funct_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.57       ( ![C:$i]:
% 0.19/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.57           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.19/0.57             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.19/0.57               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.19/0.57  thf('12', plain,
% 0.19/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.57         (~ (v1_relat_1 @ X7)
% 0.19/0.57          | ~ (v1_funct_1 @ X7)
% 0.19/0.57          | ((k1_funct_1 @ (k5_relat_1 @ X7 @ X8) @ X9)
% 0.19/0.57              = (k1_funct_1 @ X8 @ (k1_funct_1 @ X7 @ X9)))
% 0.19/0.57          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X8)))
% 0.19/0.57          | ~ (v1_funct_1 @ X8)
% 0.19/0.57          | ~ (v1_relat_1 @ X8))),
% 0.19/0.57      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.19/0.57  thf('13', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.19/0.57          | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57          | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_C_2 @ sk_B_1) @ X0)
% 0.19/0.57              = (k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_C_2 @ X0)))
% 0.19/0.57          | ~ (v1_funct_1 @ sk_C_2)
% 0.19/0.57          | ~ (v1_relat_1 @ sk_C_2))),
% 0.19/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.57  thf('14', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('15', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('16', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('17', plain, (((k5_relat_1 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('18', plain, ((v1_funct_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('19', plain, ((v1_relat_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('20', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.57          | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.19/0.57              = (k1_funct_1 @ sk_B_1 @ (k1_funct_1 @ sk_C_2 @ X0))))),
% 0.19/0.57      inference('demod', [status(thm)],
% 0.19/0.57                ['13', '14', '15', '16', '17', '18', '19'])).
% 0.19/0.57  thf('21', plain,
% 0.19/0.57      (((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57         = (k1_funct_1 @ sk_B_1 @ 
% 0.19/0.57            (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['10', '20'])).
% 0.19/0.57  thf('22', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(d8_funct_1, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.57       ( ( v2_funct_1 @ A ) <=>
% 0.19/0.57         ( ![B:$i,C:$i]:
% 0.19/0.57           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.57               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.57               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.19/0.57             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.19/0.57  thf('23', plain,
% 0.19/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.57         (~ (v2_funct_1 @ X4)
% 0.19/0.57          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.19/0.57          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X4))
% 0.19/0.57          | ((k1_funct_1 @ X4 @ X5) != (k1_funct_1 @ X4 @ X6))
% 0.19/0.57          | ((X5) = (X6))
% 0.19/0.57          | ~ (v1_funct_1 @ X4)
% 0.19/0.57          | ~ (v1_relat_1 @ X4))),
% 0.19/0.57      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.19/0.57  thf('24', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.57          | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.57          | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.57          | ((X0) = (X1))
% 0.19/0.57          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.19/0.57          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.19/0.57          | ~ (v2_funct_1 @ sk_B_1))),
% 0.19/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.57  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('27', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('28', plain, ((v2_funct_1 @ sk_B_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('29', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.57          | ((X0) = (X1))
% 0.19/0.57          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.19/0.57          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.19/0.57  thf('30', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.57          | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.57          | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) = (X0))
% 0.19/0.57          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) @ 
% 0.19/0.57               sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['21', '29'])).
% 0.19/0.57  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A)),
% 0.19/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.57  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(t125_relat_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( v1_relat_1 @ B ) =>
% 0.19/0.57       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.57         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.19/0.57  thf('33', plain,
% 0.19/0.57      (![X2 : $i, X3 : $i]:
% 0.19/0.57         (~ (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.19/0.57          | ((k8_relat_1 @ X3 @ X2) = (X2))
% 0.19/0.57          | ~ (v1_relat_1 @ X2))),
% 0.19/0.57      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.19/0.57  thf('34', plain,
% 0.19/0.57      ((~ (v1_relat_1 @ sk_C_2) | ((k8_relat_1 @ sk_A @ sk_C_2) = (sk_C_2)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.57  thf('35', plain, ((v1_relat_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('36', plain, (((k8_relat_1 @ sk_A @ sk_C_2) = (sk_C_2))),
% 0.19/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.57  thf(t123_relat_1, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( v1_relat_1 @ B ) =>
% 0.19/0.57       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.19/0.57  thf('37', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.19/0.57          | ~ (v1_relat_1 @ X0))),
% 0.19/0.57      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.57  thf(t40_funct_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.57       ( ( r2_hidden @
% 0.19/0.57           A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.19/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.19/0.57           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.19/0.57  thf('38', plain,
% 0.19/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X13 @ 
% 0.19/0.57             (k1_relat_1 @ (k5_relat_1 @ X14 @ (k6_relat_1 @ X15))))
% 0.19/0.57          | (r2_hidden @ (k1_funct_1 @ X14 @ X13) @ X15)
% 0.19/0.57          | ~ (v1_funct_1 @ X14)
% 0.19/0.57          | ~ (v1_relat_1 @ X14))),
% 0.19/0.57      inference('cnf', [status(esa)], [t40_funct_1])).
% 0.19/0.57  thf('39', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | ~ (v1_funct_1 @ X0)
% 0.19/0.57          | (r2_hidden @ (k1_funct_1 @ X0 @ X2) @ X1))),
% 0.19/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.57  thf('40', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.57         ((r2_hidden @ (k1_funct_1 @ X0 @ X2) @ X1)
% 0.19/0.57          | ~ (v1_funct_1 @ X0)
% 0.19/0.57          | ~ (v1_relat_1 @ X0)
% 0.19/0.57          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 0.19/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.57  thf('41', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.19/0.57          | ~ (v1_relat_1 @ sk_C_2)
% 0.19/0.57          | ~ (v1_funct_1 @ sk_C_2)
% 0.19/0.57          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['36', '40'])).
% 0.19/0.57  thf('42', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('43', plain, ((v1_relat_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('44', plain, ((v1_funct_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('45', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.57          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.19/0.57  thf('46', plain,
% 0.19/0.57      ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) @ sk_A)),
% 0.19/0.57      inference('sup-', [status(thm)], ['31', '45'])).
% 0.19/0.57  thf('47', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.57          | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.57          | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) = (X0)))),
% 0.19/0.57      inference('demod', [status(thm)], ['30', '46'])).
% 0.19/0.57  thf('48', plain,
% 0.19/0.57      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57          = (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57        | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A))),
% 0.19/0.57      inference('eq_res', [status(thm)], ['47'])).
% 0.19/0.57  thf('49', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A)),
% 0.19/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.57  thf('50', plain,
% 0.19/0.57      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57         = (sk_C_1 @ sk_C_2 @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.57  thf('51', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('52', plain,
% 0.19/0.57      (![X10 : $i, X11 : $i]:
% 0.19/0.57         (((k1_relat_1 @ X11) != (X10))
% 0.19/0.57          | ((k1_funct_1 @ X11 @ (sk_C_1 @ X11 @ X10)) != (sk_C_1 @ X11 @ X10))
% 0.19/0.57          | ((X11) = (k6_relat_1 @ X10))
% 0.19/0.57          | ~ (v1_funct_1 @ X11)
% 0.19/0.57          | ~ (v1_relat_1 @ X11))),
% 0.19/0.57      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.19/0.57  thf('53', plain,
% 0.19/0.57      (![X11 : $i]:
% 0.19/0.57         (~ (v1_relat_1 @ X11)
% 0.19/0.57          | ~ (v1_funct_1 @ X11)
% 0.19/0.57          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.19/0.57          | ((k1_funct_1 @ X11 @ (sk_C_1 @ X11 @ (k1_relat_1 @ X11)))
% 0.19/0.57              != (sk_C_1 @ X11 @ (k1_relat_1 @ X11))))),
% 0.19/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.19/0.57  thf('54', plain,
% 0.19/0.57      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57          != (sk_C_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))
% 0.19/0.57        | ((sk_C_2) = (k6_relat_1 @ (k1_relat_1 @ sk_C_2)))
% 0.19/0.57        | ~ (v1_funct_1 @ sk_C_2)
% 0.19/0.57        | ~ (v1_relat_1 @ sk_C_2))),
% 0.19/0.57      inference('sup-', [status(thm)], ['51', '53'])).
% 0.19/0.57  thf('55', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('56', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('57', plain, ((v1_funct_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('58', plain, ((v1_relat_1 @ sk_C_2)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('59', plain,
% 0.19/0.57      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57          != (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57        | ((sk_C_2) = (k6_relat_1 @ sk_A)))),
% 0.19/0.57      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.19/0.57  thf('60', plain, (((sk_C_2) != (k6_relat_1 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('61', plain,
% 0.19/0.57      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.19/0.57         != (sk_C_1 @ sk_C_2 @ sk_A))),
% 0.19/0.57      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.19/0.57  thf('62', plain, ($false),
% 0.19/0.57      inference('simplify_reflect-', [status(thm)], ['50', '61'])).
% 0.19/0.57  
% 0.19/0.57  % SZS output end Refutation
% 0.19/0.57  
% 0.19/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
