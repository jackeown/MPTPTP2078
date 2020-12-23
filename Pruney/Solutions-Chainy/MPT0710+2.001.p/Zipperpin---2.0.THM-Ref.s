%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rUIfbO3J4H

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:11 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 446 expanded)
%              Number of leaves         :   19 ( 126 expanded)
%              Depth                    :   28
%              Number of atoms          : 1167 (8629 expanded)
%              Number of equality atoms :   97 ( 605 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X2 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t165_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) )
             => ( ( ( k7_relat_1 @ A @ C )
                  = ( k7_relat_1 @ B @ C ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ C )
                   => ( ( k1_funct_1 @ A @ D )
                      = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                  & ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) )
               => ( ( ( k7_relat_1 @ A @ C )
                    = ( k7_relat_1 @ B @ C ) )
                <=> ! [D: $i] :
                      ( ( r2_hidden @ D @ C )
                     => ( ( k1_funct_1 @ A @ D )
                        = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t165_funct_1])).

thf('1',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('13',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf(t68_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ A ) )
              & ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) ) )
           => ( B
              = ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X10
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ X10 )
       != ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t68_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k7_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( sk_C != sk_C )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('26',plain,
    ( ( sk_C != sk_C )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_B @ sk_D_1 ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) )
    | ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference(split,[status(esa)],['31'])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X13 @ X12 ) @ X11 )
        = ( k1_funct_1 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_D_1 )
          = ( k1_funct_1 @ X0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_C )
      | ( ( k1_funct_1 @ sk_A @ X14 )
        = ( k1_funct_1 @ sk_B @ X14 ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_D_1 )
          = ( k1_funct_1 @ X0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('39',plain,
    ( ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_D_1 )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_D_1 )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_B @ sk_D_1 ) )
   <= ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('48',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_A @ sk_D_1 ) )
   <= ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
       != ( k1_funct_1 @ sk_B @ sk_D_1 ) )
      & ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_1 @ sk_C )
    | ( ( k1_funct_1 @ sk_A @ sk_D_1 )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['30','32','49'])).

thf('51',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['29','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['27','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X13 @ X12 ) @ X11 )
        = ( k1_funct_1 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X10
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ( ( k1_funct_1 @ X10 @ ( sk_D @ X8 @ X10 ) )
       != ( k1_funct_1 @ X8 @ ( sk_D @ X8 @ X10 ) ) )
      | ( ( k1_relat_1 @ X10 )
       != ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t68_funct_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
       != ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('66',plain,
    ( ! [X14: $i] :
        ( ~ ( r2_hidden @ X14 @ sk_C )
        | ( ( k1_funct_1 @ sk_A @ X14 )
          = ( k1_funct_1 @ sk_B @ X14 ) ) )
   <= ! [X14: $i] :
        ( ~ ( r2_hidden @ X14 @ sk_C )
        | ( ( k1_funct_1 @ sk_A @ X14 )
          = ( k1_funct_1 @ sk_B @ X14 ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('67',plain,
    ( ! [X14: $i] :
        ( ~ ( r2_hidden @ X14 @ sk_C )
        | ( ( k1_funct_1 @ sk_A @ X14 )
          = ( k1_funct_1 @ sk_B @ X14 ) ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['36'])).

thf('68',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_C )
      | ( ( k1_funct_1 @ sk_A @ X14 )
        = ( k1_funct_1 @ sk_B @ X14 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','32','49','67'])).

thf('69',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_C )
      | ( ( k1_funct_1 @ sk_A @ X14 )
        = ( k1_funct_1 @ sk_B @ X14 ) ) ) ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('74',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
       != ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','70','71','72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( sk_C != sk_C )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','85'])).

thf('87',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C )
    = ( k7_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['29','50'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rUIfbO3J4H
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:17:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 135 iterations in 0.120s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(t90_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.39/0.58         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i]:
% 0.39/0.58         (((k1_relat_1 @ (k7_relat_1 @ X2 @ X3))
% 0.39/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X2) @ X3))
% 0.39/0.58          | ~ (v1_relat_1 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.39/0.58  thf(t165_funct_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.39/0.58                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 0.39/0.58               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 0.39/0.58                 ( ![D:$i]:
% 0.39/0.58                   ( ( r2_hidden @ D @ C ) =>
% 0.39/0.58                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.39/0.58                    ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 0.39/0.58                  ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 0.39/0.58                    ( ![D:$i]:
% 0.39/0.58                      ( ( r2_hidden @ D @ C ) =>
% 0.39/0.58                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t165_funct_1])).
% 0.39/0.58  thf('1', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t91_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.58         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X4 @ (k1_relat_1 @ X5))
% 0.39/0.58          | ((k1_relat_1 @ (k7_relat_1 @ X5 @ X4)) = (X4))
% 0.39/0.58          | ~ (v1_relat_1 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_A)
% 0.39/0.58        | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('5', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      ((((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) = (sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['0', '5'])).
% 0.39/0.58  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('8', plain, (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf(fc8_funct_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.39/0.58         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X6)
% 0.39/0.58          | ~ (v1_relat_1 @ X6)
% 0.39/0.58          | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X6)
% 0.39/0.58          | ~ (v1_relat_1 @ X6)
% 0.39/0.58          | (v1_funct_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X6)
% 0.39/0.58          | ~ (v1_relat_1 @ X6)
% 0.39/0.58          | (v1_funct_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X6)
% 0.39/0.58          | ~ (v1_relat_1 @ X6)
% 0.39/0.58          | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.39/0.58  thf('13', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X4 @ (k1_relat_1 @ X5))
% 0.39/0.58          | ((k1_relat_1 @ (k7_relat_1 @ X5 @ X4)) = (X4))
% 0.39/0.58          | ~ (v1_relat_1 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.58        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('17', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('18', plain, (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf(t68_funct_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.58           ( ( ( ( k1_relat_1 @ B ) = ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ A ) ) & 
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.58                   ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 0.39/0.58             ( ( B ) = ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X8)
% 0.39/0.58          | ~ (v1_funct_1 @ X8)
% 0.39/0.58          | ((X10) = (k7_relat_1 @ X8 @ X9))
% 0.39/0.58          | (r2_hidden @ (sk_D @ X8 @ X10) @ (k1_relat_1 @ X10))
% 0.39/0.58          | ((k1_relat_1 @ X10) != (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.39/0.58          | ~ (v1_funct_1 @ X10)
% 0.39/0.58          | ~ (v1_relat_1 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t68_funct_1])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_relat_1 @ X0) != (sk_C))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_D @ sk_A @ X0) @ (k1_relat_1 @ X0))
% 0.39/0.58          | ((X0) = (k7_relat_1 @ sk_A @ sk_C))
% 0.39/0.58          | ~ (v1_funct_1 @ sk_A)
% 0.39/0.58          | ~ (v1_relat_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf('21', plain, ((v1_funct_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_relat_1 @ X0) != (sk_C))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_D @ sk_A @ X0) @ (k1_relat_1 @ X0))
% 0.39/0.58          | ((X0) = (k7_relat_1 @ sk_A @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      ((((sk_C) != (sk_C))
% 0.39/0.58        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 0.39/0.58        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ 
% 0.39/0.58           (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.39/0.58        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '23'])).
% 0.39/0.58  thf('25', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      ((((sk_C) != (sk_C))
% 0.39/0.58        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 0.39/0.58        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.39/0.58        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((((k1_funct_1 @ sk_A @ sk_D_1) != (k1_funct_1 @ sk_B @ sk_D_1))
% 0.39/0.58        | ((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      ((((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C)))
% 0.39/0.58         <= (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))))),
% 0.39/0.58      inference('split', [status(esa)], ['28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) | 
% 0.39/0.58       ~ (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1)))),
% 0.39/0.58      inference('split', [status(esa)], ['28'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (((r2_hidden @ sk_D_1 @ sk_C)
% 0.39/0.58        | ((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (((r2_hidden @ sk_D_1 @ sk_C)) | 
% 0.39/0.58       ~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['31'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (((r2_hidden @ sk_D_1 @ sk_C)) <= (((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['31'])).
% 0.39/0.58  thf(t72_funct_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.58       ( ( r2_hidden @ A @ B ) =>
% 0.39/0.58         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.39/0.58          | ~ (v1_relat_1 @ X13)
% 0.39/0.58          | ~ (v1_funct_1 @ X13)
% 0.39/0.58          | ((k1_funct_1 @ (k7_relat_1 @ X13 @ X12) @ X11)
% 0.39/0.58              = (k1_funct_1 @ X13 @ X11)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_D_1)
% 0.39/0.58             = (k1_funct_1 @ X0 @ sk_D_1))
% 0.39/0.58           | ~ (v1_funct_1 @ X0)
% 0.39/0.58           | ~ (v1_relat_1 @ X0)))
% 0.39/0.58         <= (((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X14 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X14 @ sk_C)
% 0.39/0.58          | ((k1_funct_1 @ sk_A @ X14) = (k1_funct_1 @ sk_B @ X14))
% 0.39/0.58          | ((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))
% 0.39/0.58         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))))),
% 0.39/0.58      inference('split', [status(esa)], ['36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_D_1)
% 0.39/0.58             = (k1_funct_1 @ X0 @ sk_D_1))
% 0.39/0.58           | ~ (v1_funct_1 @ X0)
% 0.39/0.58           | ~ (v1_relat_1 @ X0)))
% 0.39/0.58         <= (((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (((((k1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_D_1)
% 0.39/0.58           = (k1_funct_1 @ sk_B @ sk_D_1))
% 0.39/0.58         | ~ (v1_relat_1 @ sk_B)
% 0.39/0.58         | ~ (v1_funct_1 @ sk_B)))
% 0.39/0.58         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.39/0.58             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.39/0.58  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      ((((k1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_D_1)
% 0.39/0.58          = (k1_funct_1 @ sk_B @ sk_D_1)))
% 0.39/0.58         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.39/0.58             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (((((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1))
% 0.39/0.58         | ~ (v1_relat_1 @ sk_A)
% 0.39/0.58         | ~ (v1_funct_1 @ sk_A)))
% 0.39/0.58         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.39/0.58             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['35', '42'])).
% 0.39/0.58  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      ((((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1)))
% 0.39/0.58         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.39/0.58             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      ((((k1_funct_1 @ sk_A @ sk_D_1) != (k1_funct_1 @ sk_B @ sk_D_1)))
% 0.39/0.58         <= (~ (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.39/0.58      inference('split', [status(esa)], ['28'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      ((((k1_funct_1 @ sk_A @ sk_D_1) != (k1_funct_1 @ sk_A @ sk_D_1)))
% 0.39/0.58         <= (~ (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1))) & 
% 0.39/0.58             (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.39/0.58             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) | 
% 0.39/0.58       ~ ((r2_hidden @ sk_D_1 @ sk_C)) | 
% 0.39/0.58       (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['30', '32', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['29', '50'])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C))),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['27', '51'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.58        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '52'])).
% 0.39/0.58  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (((r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.39/0.58  thf('57', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.58        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['11', '56'])).
% 0.39/0.58  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('59', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      ((r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.39/0.58          | ~ (v1_relat_1 @ X13)
% 0.39/0.58          | ~ (v1_funct_1 @ X13)
% 0.39/0.58          | ((k1_funct_1 @ (k7_relat_1 @ X13 @ X12) @ X11)
% 0.39/0.58              = (k1_funct_1 @ X13 @ X11)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_C) @ 
% 0.39/0.58            (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.39/0.58            = (k1_funct_1 @ X0 @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X8)
% 0.39/0.58          | ~ (v1_funct_1 @ X8)
% 0.39/0.58          | ((X10) = (k7_relat_1 @ X8 @ X9))
% 0.39/0.58          | ((k1_funct_1 @ X10 @ (sk_D @ X8 @ X10))
% 0.39/0.58              != (k1_funct_1 @ X8 @ (sk_D @ X8 @ X10)))
% 0.39/0.58          | ((k1_relat_1 @ X10) != (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.39/0.58          | ~ (v1_funct_1 @ X10)
% 0.39/0.58          | ~ (v1_relat_1 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t68_funct_1])).
% 0.39/0.58  thf('64', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_funct_1 @ sk_B @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.39/0.58            != (k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))
% 0.39/0.58          | ~ (v1_relat_1 @ sk_B)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58              != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.39/0.58          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ sk_A)
% 0.39/0.58          | ~ (v1_relat_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      ((r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      ((![X14 : $i]:
% 0.39/0.58          (~ (r2_hidden @ X14 @ sk_C)
% 0.39/0.58           | ((k1_funct_1 @ sk_A @ X14) = (k1_funct_1 @ sk_B @ X14))))
% 0.39/0.58         <= ((![X14 : $i]:
% 0.39/0.58                (~ (r2_hidden @ X14 @ sk_C)
% 0.39/0.58                 | ((k1_funct_1 @ sk_A @ X14) = (k1_funct_1 @ sk_B @ X14)))))),
% 0.39/0.58      inference('split', [status(esa)], ['36'])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      ((![X14 : $i]:
% 0.39/0.58          (~ (r2_hidden @ X14 @ sk_C)
% 0.39/0.58           | ((k1_funct_1 @ sk_A @ X14) = (k1_funct_1 @ sk_B @ X14)))) | 
% 0.39/0.58       (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['36'])).
% 0.39/0.58  thf('68', plain,
% 0.39/0.58      ((![X14 : $i]:
% 0.39/0.58          (~ (r2_hidden @ X14 @ sk_C)
% 0.39/0.58           | ((k1_funct_1 @ sk_A @ X14) = (k1_funct_1 @ sk_B @ X14))))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['30', '32', '49', '67'])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      (![X14 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X14 @ sk_C)
% 0.39/0.58          | ((k1_funct_1 @ sk_A @ X14) = (k1_funct_1 @ sk_B @ X14)))),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.39/0.58  thf('70', plain,
% 0.39/0.58      (((k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.39/0.58         = (k1_funct_1 @ sk_B @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['65', '69'])).
% 0.39/0.58  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('73', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('74', plain, ((v1_funct_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('76', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.39/0.58            != (k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))
% 0.39/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.39/0.58          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)],
% 0.39/0.58                ['64', '70', '71', '72', '73', '74', '75'])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.39/0.58          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.58  thf('78', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ sk_B)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.39/0.58          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '77'])).
% 0.39/0.58  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('81', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.39/0.58          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.39/0.58          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.39/0.58  thf('82', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ sk_B)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.58          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.39/0.58          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '81'])).
% 0.39/0.58  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('84', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('85', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.39/0.58          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.39/0.58  thf('86', plain,
% 0.39/0.58      ((((sk_C) != (sk_C))
% 0.39/0.58        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '85'])).
% 0.39/0.58  thf('87', plain, (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['86'])).
% 0.39/0.58  thf('88', plain,
% 0.39/0.58      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['29', '50'])).
% 0.39/0.58  thf('89', plain, ($false),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
