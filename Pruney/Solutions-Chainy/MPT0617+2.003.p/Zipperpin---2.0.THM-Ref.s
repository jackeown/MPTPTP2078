%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SJNhoTXFGr

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:19 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 272 expanded)
%              Number of leaves         :   15 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :  855 (4662 expanded)
%              Number of equality atoms :   54 ( 398 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t9_funct_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( A = B )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
              <=> ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0 = sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( X10
       != ( k1_funct_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X11 )
        = ( k1_funct_1 @ sk_B @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X11 )
        = ( k1_funct_1 @ sk_B @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X9 )
      | ( X10
        = ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X9 )
      | ( X10
        = ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ( sk_B = sk_A )
    | ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,
    ( ( sk_B = sk_A )
    | ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_D @ sk_A @ sk_B )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['21','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_B = sk_A )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('60',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_D @ sk_A @ sk_B )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('62',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['50','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SJNhoTXFGr
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.32  % CPULimit   : 60
% 0.17/0.32  % DateTime   : Tue Dec  1 10:50:50 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.32  % Running portfolio for 600 s
% 0.17/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.17/0.32  % Number of cores: 8
% 0.17/0.33  % Python version: Python 3.6.8
% 0.17/0.33  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 192 iterations in 0.152s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(t9_funct_1, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.44/0.62               ( ![C:$i]:
% 0.44/0.62                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.62                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.44/0.62             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62              ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.44/0.62                  ( ![C:$i]:
% 0.44/0.62                    ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.62                      ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.44/0.62                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t9_funct_1])).
% 0.44/0.62  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(d2_relat_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( v1_relat_1 @ B ) =>
% 0.44/0.62           ( ( ( A ) = ( B ) ) <=>
% 0.44/0.62             ( ![C:$i,D:$i]:
% 0.44/0.62               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 0.44/0.62                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.44/0.62          | ((X1) = (X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.44/0.62  thf(t20_relat_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ C ) =>
% 0.44/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.44/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.44/0.62           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.62         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.44/0.62          | (r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.44/0.62          | ~ (v1_relat_1 @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((X0) = (X1))
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.44/0.62          | ~ (v1_relat_1 @ X1)
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X1)
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.44/0.62          | ((X0) = (X1))
% 0.44/0.62          | ~ (v1_relat_1 @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['3'])).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.62         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.44/0.62          | (r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.44/0.62          | ~ (v1_relat_1 @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X1)
% 0.44/0.62          | ((X1) = (X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.44/0.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((X1) = (X0))
% 0.44/0.62          | ~ (v1_relat_1 @ X1))),
% 0.44/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_C @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((X0) = (sk_A))
% 0.44/0.62          | ~ (v1_relat_1 @ sk_A)
% 0.44/0.62          | (r2_hidden @ (sk_C @ sk_A @ X0) @ (k1_relat_1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['0', '7'])).
% 0.44/0.62  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_C @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((X0) = (sk_A))
% 0.44/0.62          | (r2_hidden @ (sk_C @ sk_A @ X0) @ (k1_relat_1 @ X0)))),
% 0.44/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      ((((sk_B) = (sk_A))
% 0.44/0.62        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.62        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.44/0.62      inference('eq_fact', [status(thm)], ['10'])).
% 0.44/0.62  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      ((((sk_B) = (sk_A))
% 0.44/0.62        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.44/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.44/0.62  thf('14', plain, (((sk_A) != (sk_B))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('15', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf(t8_funct_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.44/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.44/0.62           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.44/0.62          | ((X10) != (k1_funct_1 @ X9 @ X8))
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ X8 @ X10) @ X9)
% 0.44/0.62          | ~ (v1_funct_1 @ X9)
% 0.44/0.62          | ~ (v1_relat_1 @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X9)
% 0.44/0.62          | ~ (v1_funct_1 @ X9)
% 0.44/0.62          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.44/0.62          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (((r2_hidden @ 
% 0.44/0.62         (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.44/0.62          (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.44/0.62         sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['15', '17'])).
% 0.44/0.62  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      ((r2_hidden @ 
% 0.44/0.62        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.44/0.63         (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.44/0.63        sk_B)),
% 0.44/0.63      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.44/0.63  thf('22', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.44/0.63  thf('23', plain,
% 0.44/0.63      (![X11 : $i]:
% 0.44/0.63         (((k1_funct_1 @ sk_A @ X11) = (k1_funct_1 @ sk_B @ X11))
% 0.44/0.63          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('24', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      (![X11 : $i]:
% 0.44/0.63         (((k1_funct_1 @ sk_A @ X11) = (k1_funct_1 @ sk_B @ X11))
% 0.44/0.63          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.44/0.63  thf('26', plain,
% 0.44/0.63      (((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.44/0.63         = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['22', '25'])).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X0)
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.44/0.63          | ((X1) = (X0))
% 0.44/0.63          | ~ (v1_relat_1 @ X1))),
% 0.44/0.63      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.63         (~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X9)
% 0.44/0.63          | ((X10) = (k1_funct_1 @ X9 @ X8))
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (v1_relat_1 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X0)
% 0.44/0.63          | ((X0) = (X1))
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.44/0.63          | ~ (v1_relat_1 @ X1)
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.63  thf('30', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ X1)
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.44/0.63          | ((X0) = (X1))
% 0.44/0.63          | ~ (v1_relat_1 @ X0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.44/0.63  thf('31', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.63         (~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X9)
% 0.44/0.63          | ((X10) = (k1_funct_1 @ X9 @ X8))
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (v1_relat_1 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.44/0.63  thf('32', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X1)
% 0.44/0.63          | ((X1) = (X0))
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | ~ (v1_funct_1 @ X1)
% 0.44/0.63          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.63  thf('33', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1)))
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 0.44/0.63          | ~ (v1_funct_1 @ X1)
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | ((X1) = (X0))
% 0.44/0.63          | ~ (v1_relat_1 @ X1))),
% 0.44/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.44/0.63  thf('34', plain,
% 0.44/0.63      ((((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.44/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.63        | ((sk_B) = (sk_A))
% 0.44/0.63        | ~ (v1_relat_1 @ sk_A)
% 0.44/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.63        | ((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.44/0.63        | ~ (v1_funct_1 @ sk_A))),
% 0.44/0.63      inference('sup+', [status(thm)], ['26', '33'])).
% 0.44/0.63  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('38', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      ((((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.44/0.63        | ((sk_B) = (sk_A))
% 0.44/0.63        | ((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))))),
% 0.44/0.63      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.44/0.63  thf('40', plain,
% 0.44/0.63      ((((sk_B) = (sk_A))
% 0.44/0.63        | ((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))))),
% 0.44/0.63      inference('simplify', [status(thm)], ['39'])).
% 0.44/0.63  thf('41', plain, (((sk_A) != (sk_B))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('42', plain,
% 0.44/0.63      (((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.44/0.63  thf('43', plain,
% 0.44/0.63      ((r2_hidden @ 
% 0.44/0.63        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_B)),
% 0.44/0.63      inference('demod', [status(thm)], ['21', '42'])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X0)
% 0.44/0.63          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.44/0.63               X1)
% 0.44/0.63          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.44/0.63               X0)
% 0.44/0.63          | ((X1) = (X0))
% 0.44/0.63          | ~ (v1_relat_1 @ X1))),
% 0.44/0.63      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.44/0.63        | ((sk_B) = (sk_A))
% 0.44/0.63        | ~ (r2_hidden @ 
% 0.44/0.63             (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A)
% 0.44/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.44/0.63  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('48', plain,
% 0.44/0.63      ((((sk_B) = (sk_A))
% 0.44/0.63        | ~ (r2_hidden @ 
% 0.44/0.63             (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.44/0.63  thf('49', plain, (((sk_A) != (sk_B))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('50', plain,
% 0.44/0.63      (~ (r2_hidden @ 
% 0.44/0.63          (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A)),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.44/0.63  thf('51', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.44/0.63  thf('52', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('53', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X9)
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.44/0.63          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.63  thf('54', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A)
% 0.44/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.44/0.63          | ~ (v1_relat_1 @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.44/0.63  thf('55', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('57', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.44/0.63  thf('58', plain,
% 0.44/0.63      ((r2_hidden @ 
% 0.44/0.63        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.44/0.63         (k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))) @ 
% 0.44/0.63        sk_A)),
% 0.44/0.63      inference('sup-', [status(thm)], ['51', '57'])).
% 0.44/0.63  thf('59', plain,
% 0.44/0.63      (((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.44/0.63         = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['22', '25'])).
% 0.44/0.63  thf('60', plain,
% 0.44/0.63      ((r2_hidden @ 
% 0.44/0.63        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.44/0.63         (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.44/0.63        sk_A)),
% 0.44/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.63  thf('61', plain,
% 0.44/0.63      (((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.44/0.63  thf('62', plain,
% 0.44/0.63      ((r2_hidden @ 
% 0.44/0.63        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A)),
% 0.44/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.44/0.63  thf('63', plain, ($false), inference('demod', [status(thm)], ['50', '62'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
