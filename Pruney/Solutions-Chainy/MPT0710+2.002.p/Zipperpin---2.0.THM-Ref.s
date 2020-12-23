%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PVb6pD6VhV

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 559 expanded)
%              Number of leaves         :   19 ( 157 expanded)
%              Depth                    :   29
%              Number of atoms          : 1279 (10728 expanded)
%              Number of equality atoms :  107 ( 752 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_relat_1 @ X3 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('13',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_relat_1 @ X3 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X8
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k3_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('34',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 )
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_D_1 )
      = ( k1_funct_1 @ sk_A @ sk_D_1 ) )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ sk_C ) ),
    inference(split,[status(esa)],['31'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ~ ( r2_hidden @ X12 @ sk_C )
      | ( ( k1_funct_1 @ sk_A @ X12 )
        = ( k1_funct_1 @ sk_B @ X12 ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 )
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ X0 )
          = ( k1_funct_1 @ sk_B @ X0 ) ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ X0 )
          = ( k1_funct_1 @ sk_B @ X0 ) ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_D_1 )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_B @ sk_D_1 ) )
   <= ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
     != ( k1_funct_1 @ sk_A @ sk_D_1 ) )
   <= ( ( ( k1_funct_1 @ sk_A @ sk_D_1 )
       != ( k1_funct_1 @ sk_B @ sk_D_1 ) )
      & ( ( k7_relat_1 @ sk_A @ sk_C )
        = ( k7_relat_1 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C )
     != ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_1 @ sk_C )
    | ( ( k1_funct_1 @ sk_A @ sk_D_1 )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['30','32','55'])).

thf('57',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['29','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['27','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('68',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 )
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('75',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_C )
        | ( ( k1_funct_1 @ sk_A @ X12 )
          = ( k1_funct_1 @ sk_B @ X12 ) ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_C )
        | ( ( k1_funct_1 @ sk_A @ X12 )
          = ( k1_funct_1 @ sk_B @ X12 ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('76',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_C )
        | ( ( k1_funct_1 @ sk_A @ X12 )
          = ( k1_funct_1 @ sk_B @ X12 ) ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C )
      = ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['42'])).

thf('77',plain,(
    ! [X12: $i] :
      ( ~ ( r2_hidden @ X12 @ sk_C )
      | ( ( k1_funct_1 @ sk_A @ X12 )
        = ( k1_funct_1 @ sk_B @ X12 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','32','55','76'])).

thf('78',plain,(
    ! [X12: $i] :
      ( ~ ( r2_hidden @ X12 @ sk_C )
      | ( ( k1_funct_1 @ sk_A @ X12 )
        = ( k1_funct_1 @ sk_B @ X12 ) ) ) ),
    inference(simpl_trail,[status(thm)],['75','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X8
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ( ( k1_funct_1 @ X8 @ ( sk_D @ X6 @ X8 ) )
       != ( k1_funct_1 @ X6 @ ( sk_D @ X6 @ X8 ) ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k3_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t68_funct_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
       != ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('84',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) )
       != ( k1_funct_1 @ sk_A @ ( sk_D @ sk_A @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ sk_C )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( sk_C
       != ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( sk_C != sk_C )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','95'])).

thf('97',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C )
    = ( k7_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['29','56'])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PVb6pD6VhV
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 139 iterations in 0.125s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(t90_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.20/0.57         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.57            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.20/0.57          | ~ (v1_relat_1 @ X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.57  thf(t165_funct_1, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.57                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.57               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 0.20/0.57                 ( ![D:$i]:
% 0.20/0.57                   ( ( r2_hidden @ D @ C ) =>
% 0.20/0.57                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.57              ( ![C:$i]:
% 0.20/0.57                ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.57                    ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.57                  ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 0.20/0.57                    ( ![D:$i]:
% 0.20/0.57                      ( ( r2_hidden @ D @ C ) =>
% 0.20/0.57                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t165_funct_1])).
% 0.20/0.57  thf('1', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t91_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.57         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X2 @ (k1_relat_1 @ X3))
% 0.20/0.57          | ((k1_relat_1 @ (k7_relat_1 @ X3 @ X2)) = (X2))
% 0.20/0.57          | ~ (v1_relat_1 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.57        | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('5', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      ((((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) = (sk_C))
% 0.20/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['0', '5'])).
% 0.20/0.57  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('8', plain, (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf(fc8_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.57       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.20/0.57         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X4)
% 0.20/0.57          | ~ (v1_relat_1 @ X4)
% 0.20/0.57          | (v1_relat_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X4)
% 0.20/0.57          | ~ (v1_relat_1 @ X4)
% 0.20/0.57          | (v1_funct_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X4)
% 0.20/0.57          | ~ (v1_relat_1 @ X4)
% 0.20/0.57          | (v1_funct_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X4)
% 0.20/0.57          | ~ (v1_relat_1 @ X4)
% 0.20/0.57          | (v1_relat_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.20/0.57  thf('13', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X2 @ (k1_relat_1 @ X3))
% 0.20/0.57          | ((k1_relat_1 @ (k7_relat_1 @ X3 @ X2)) = (X2))
% 0.20/0.57          | ~ (v1_relat_1 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.57        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('17', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('18', plain, (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf(t68_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.57       ( ![C:$i]:
% 0.20/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.57           ( ( ( ( k1_relat_1 @ B ) = ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ A ) ) & 
% 0.20/0.57               ( ![D:$i]:
% 0.20/0.57                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.57                   ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 0.20/0.57             ( ( B ) = ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X6)
% 0.20/0.57          | ~ (v1_funct_1 @ X6)
% 0.20/0.57          | ((X8) = (k7_relat_1 @ X6 @ X7))
% 0.20/0.57          | (r2_hidden @ (sk_D @ X6 @ X8) @ (k1_relat_1 @ X8))
% 0.20/0.57          | ((k1_relat_1 @ X8) != (k3_xboole_0 @ (k1_relat_1 @ X6) @ X7))
% 0.20/0.57          | ~ (v1_funct_1 @ X8)
% 0.20/0.57          | ~ (v1_relat_1 @ X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [t68_funct_1])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_relat_1 @ X0) != (sk_C))
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_funct_1 @ X0)
% 0.20/0.57          | (r2_hidden @ (sk_D @ sk_A @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.57          | ((X0) = (k7_relat_1 @ sk_A @ sk_C))
% 0.20/0.57          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.57          | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf('21', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_relat_1 @ X0) != (sk_C))
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_funct_1 @ X0)
% 0.20/0.57          | (r2_hidden @ (sk_D @ sk_A @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.57          | ((X0) = (k7_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      ((((sk_C) != (sk_C))
% 0.20/0.57        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 0.20/0.57        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ 
% 0.20/0.57           (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['17', '23'])).
% 0.20/0.57  thf('25', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      ((((sk_C) != (sk_C))
% 0.20/0.57        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 0.20/0.57        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.20/0.57        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.20/0.57        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      ((((k1_funct_1 @ sk_A @ sk_D_1) != (k1_funct_1 @ sk_B @ sk_D_1))
% 0.20/0.57        | ((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      ((((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57         <= (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('split', [status(esa)], ['28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) | 
% 0.20/0.57       ~ (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1)))),
% 0.20/0.57      inference('split', [status(esa)], ['28'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (((r2_hidden @ sk_D_1 @ sk_C)
% 0.20/0.57        | ((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (((r2_hidden @ sk_D_1 @ sk_C)) | 
% 0.20/0.57       ~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (((r2_hidden @ sk_D_1 @ sk_C)) <= (((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['31'])).
% 0.20/0.57  thf('34', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf(t70_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.20/0.57         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X9 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)))
% 0.20/0.57          | ((k1_funct_1 @ (k7_relat_1 @ X10 @ X11) @ X9)
% 0.20/0.57              = (k1_funct_1 @ X10 @ X9))
% 0.20/0.57          | ~ (v1_funct_1 @ X10)
% 0.20/0.57          | ~ (v1_relat_1 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.57          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.57          | ((k1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C) @ X0)
% 0.20/0.57              = (k1_funct_1 @ sk_A @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.57  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('38', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.57          | ((k1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C) @ X0)
% 0.20/0.57              = (k1_funct_1 @ sk_A @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      ((((k1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_D_1)
% 0.20/0.57          = (k1_funct_1 @ sk_A @ sk_D_1)))
% 0.20/0.57         <= (((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['33', '39'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (((r2_hidden @ sk_D_1 @ sk_C)) <= (((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['31'])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (![X12 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X12 @ sk_C)
% 0.20/0.57          | ((k1_funct_1 @ sk_A @ X12) = (k1_funct_1 @ sk_B @ X12))
% 0.20/0.57          | ((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('split', [status(esa)], ['42'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X9 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)))
% 0.20/0.57          | ((k1_funct_1 @ (k7_relat_1 @ X10 @ X11) @ X9)
% 0.20/0.57              = (k1_funct_1 @ X10 @ X9))
% 0.20/0.57          | ~ (v1_funct_1 @ X10)
% 0.20/0.57          | ~ (v1_relat_1 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.20/0.57           | ~ (v1_relat_1 @ sk_B)
% 0.20/0.57           | ~ (v1_funct_1 @ sk_B)
% 0.20/0.57           | ((k1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C) @ X0)
% 0.20/0.57               = (k1_funct_1 @ sk_B @ X0))))
% 0.20/0.57         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.57  thf('46', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('split', [status(esa)], ['42'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.57           | ((k1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C) @ X0)
% 0.20/0.57               = (k1_funct_1 @ sk_B @ X0))))
% 0.20/0.57         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      ((((k1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_D_1)
% 0.20/0.57          = (k1_funct_1 @ sk_B @ sk_D_1)))
% 0.20/0.57         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.20/0.57             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['41', '50'])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      ((((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1)))
% 0.20/0.57         <= ((((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.20/0.57             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['40', '51'])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      ((((k1_funct_1 @ sk_A @ sk_D_1) != (k1_funct_1 @ sk_B @ sk_D_1)))
% 0.20/0.57         <= (~ (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.20/0.57      inference('split', [status(esa)], ['28'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      ((((k1_funct_1 @ sk_A @ sk_D_1) != (k1_funct_1 @ sk_A @ sk_D_1)))
% 0.20/0.57         <= (~ (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1))) & 
% 0.20/0.57             (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) & 
% 0.20/0.57             ((r2_hidden @ sk_D_1 @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))) | 
% 0.20/0.57       ~ ((r2_hidden @ sk_D_1 @ sk_C)) | 
% 0.20/0.57       (((k1_funct_1 @ sk_A @ sk_D_1) = (k1_funct_1 @ sk_B @ sk_D_1)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (~ (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['30', '32', '55'])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['29', '56'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C))),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['27', '57'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.57        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.20/0.57        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '58'])).
% 0.20/0.57  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      (((r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)
% 0.20/0.57        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.57        | (r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '62'])).
% 0.20/0.57  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      ((r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)),
% 0.20/0.57      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.57  thf('67', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X9 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)))
% 0.20/0.57          | ((k1_funct_1 @ (k7_relat_1 @ X10 @ X11) @ X9)
% 0.20/0.57              = (k1_funct_1 @ X10 @ X9))
% 0.20/0.57          | ~ (v1_funct_1 @ X10)
% 0.20/0.57          | ~ (v1_relat_1 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.57          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.57          | ((k1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C) @ X0)
% 0.20/0.57              = (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.57  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('72', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.57          | ((k1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C) @ X0)
% 0.20/0.57              = (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      (((k1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C) @ 
% 0.20/0.57         (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57         = (k1_funct_1 @ sk_B @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['66', '72'])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      ((r2_hidden @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)) @ sk_C)),
% 0.20/0.57      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      ((![X12 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X12 @ sk_C)
% 0.20/0.57           | ((k1_funct_1 @ sk_A @ X12) = (k1_funct_1 @ sk_B @ X12))))
% 0.20/0.57         <= ((![X12 : $i]:
% 0.20/0.57                (~ (r2_hidden @ X12 @ sk_C)
% 0.20/0.57                 | ((k1_funct_1 @ sk_A @ X12) = (k1_funct_1 @ sk_B @ X12)))))),
% 0.20/0.57      inference('split', [status(esa)], ['42'])).
% 0.20/0.57  thf('76', plain,
% 0.20/0.57      ((![X12 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X12 @ sk_C)
% 0.20/0.57           | ((k1_funct_1 @ sk_A @ X12) = (k1_funct_1 @ sk_B @ X12)))) | 
% 0.20/0.57       (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['42'])).
% 0.20/0.57  thf('77', plain,
% 0.20/0.57      ((![X12 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X12 @ sk_C)
% 0.20/0.57           | ((k1_funct_1 @ sk_A @ X12) = (k1_funct_1 @ sk_B @ X12))))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['30', '32', '55', '76'])).
% 0.20/0.57  thf('78', plain,
% 0.20/0.57      (![X12 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X12 @ sk_C)
% 0.20/0.57          | ((k1_funct_1 @ sk_A @ X12) = (k1_funct_1 @ sk_B @ X12)))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['75', '77'])).
% 0.20/0.57  thf('79', plain,
% 0.20/0.57      (((k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57         = (k1_funct_1 @ sk_B @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['74', '78'])).
% 0.20/0.57  thf('80', plain,
% 0.20/0.57      (((k1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C) @ 
% 0.20/0.57         (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57         = (k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.57      inference('demod', [status(thm)], ['73', '79'])).
% 0.20/0.57  thf('81', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X6)
% 0.20/0.57          | ~ (v1_funct_1 @ X6)
% 0.20/0.57          | ((X8) = (k7_relat_1 @ X6 @ X7))
% 0.20/0.57          | ((k1_funct_1 @ X8 @ (sk_D @ X6 @ X8))
% 0.20/0.57              != (k1_funct_1 @ X6 @ (sk_D @ X6 @ X8)))
% 0.20/0.57          | ((k1_relat_1 @ X8) != (k3_xboole_0 @ (k1_relat_1 @ X6) @ X7))
% 0.20/0.57          | ~ (v1_funct_1 @ X8)
% 0.20/0.57          | ~ (v1_relat_1 @ X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [t68_funct_1])).
% 0.20/0.57  thf('82', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57            != (k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))
% 0.20/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57              != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.20/0.57          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.20/0.57          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.57          | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.57  thf('83', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)) = (sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('84', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('86', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C)))
% 0.20/0.57            != (k1_funct_1 @ sk_A @ (sk_D @ sk_A @ (k7_relat_1 @ sk_B @ sk_C))))
% 0.20/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.20/0.57          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.20/0.57  thf('87', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.20/0.57          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.20/0.57          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ sk_B)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.20/0.57          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['10', '87'])).
% 0.20/0.57  thf('89', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('90', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('91', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_C))
% 0.20/0.57          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 0.20/0.57          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.20/0.57  thf('92', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ sk_B)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.57          | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.20/0.57          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '91'])).
% 0.20/0.57  thf('93', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('94', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('95', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ X0))
% 0.20/0.57          | ((sk_C) != (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.20/0.57  thf('96', plain,
% 0.20/0.57      ((((sk_C) != (sk_C))
% 0.20/0.57        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['8', '95'])).
% 0.20/0.57  thf('97', plain, (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))),
% 0.20/0.57      inference('simplify', [status(thm)], ['96'])).
% 0.20/0.57  thf('98', plain,
% 0.20/0.57      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['29', '56'])).
% 0.20/0.57  thf('99', plain, ($false),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
