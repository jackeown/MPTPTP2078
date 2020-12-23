%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gu26ATlUcH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:10 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 988 expanded)
%              Number of leaves         :   19 ( 280 expanded)
%              Depth                    :   24
%              Number of atoms          : 1507 (16070 expanded)
%              Number of equality atoms :  108 (1812 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t44_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ( ( k5_relat_1 @ A @ B )
                  = A ) )
             => ( B
                = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_funct_1])).

thf('0',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != X19 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X19 ) @ X19 )
      | ( X20
        = ( k6_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X20
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ ( k1_relat_1 @ X20 ) ) @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    sk_B
 != ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('14',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X9 )
      | ( X11
       != ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ( X10
       != ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ X9 @ X8 )
        = k1_xboole_0 )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ X9 @ X8 )
        = k1_xboole_0 )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

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

thf('32',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k2_relat_1 @ X13 ) )
      | ( X16
        = ( k1_funct_1 @ X13 @ ( sk_D_2 @ X16 @ X13 ) ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('33',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( X16
        = ( k1_funct_1 @ X13 @ ( sk_D_2 @ X16 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ X0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('39',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('40',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X13 ) @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ X0 @ sk_A ) ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ X0 @ sk_A ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ X0 ) @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ X1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('68',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X13 ) @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( X11
        = ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ X0 ) @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ X0 ) @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('79',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( X16
        = ( k1_funct_1 @ X13 @ ( sk_D_2 @ X16 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('80',plain,
    ( ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ X0 ) @ sk_A )
      | ( X0
        = ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['77','83'])).

thf('85',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
      = ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != X19 )
      | ( ( k1_funct_1 @ X20 @ ( sk_C_1 @ X20 @ X19 ) )
       != ( sk_C_1 @ X20 @ X19 ) )
      | ( X20
        = ( k6_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('88',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X20
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ( ( k1_funct_1 @ X20 @ ( sk_C_1 @ X20 @ ( k1_relat_1 @ X20 ) ) )
       != ( sk_C_1 @ X20 @ ( k1_relat_1 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('96',plain,(
    ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
 != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['85','96'])).

thf('98',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ k1_xboole_0 ) @ sk_B ),
    inference(demod,[status(thm)],['20','97'])).

thf('99',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('101',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('103',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A )
    | ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
 != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('107',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['85','96'])).

thf('108',plain,(
    k1_xboole_0
 != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ X0 ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ k1_xboole_0 ) @ sk_A ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ X9 @ X8 )
        = k1_xboole_0 )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('114',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( X11
        = ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( X2
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['112','116'])).

thf('118',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('119',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('122',plain,
    ( ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    k1_xboole_0
 != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gu26ATlUcH
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.63  % Solved by: fo/fo7.sh
% 0.39/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.63  % done 137 iterations in 0.199s
% 0.39/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.63  % SZS output start Refutation
% 0.39/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.63  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.39/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.39/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.63  thf(t44_funct_1, conjecture,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.63       ( ![B:$i]:
% 0.39/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.63           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.39/0.63               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.39/0.63             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.39/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.63    (~( ![A:$i]:
% 0.39/0.63        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.63          ( ![B:$i]:
% 0.39/0.63            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.63              ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.39/0.63                  ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.39/0.63                ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )),
% 0.39/0.63    inference('cnf.neg', [status(esa)], [t44_funct_1])).
% 0.39/0.63  thf('0', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(t34_funct_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.63       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.39/0.63         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.39/0.63           ( ![C:$i]:
% 0.39/0.63             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.39/0.63  thf('1', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         (((k1_relat_1 @ X20) != (X19))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ X20 @ X19) @ X19)
% 0.39/0.63          | ((X20) = (k6_relat_1 @ X19))
% 0.39/0.63          | ~ (v1_funct_1 @ X20)
% 0.39/0.63          | ~ (v1_relat_1 @ X20))),
% 0.39/0.63      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.39/0.63  thf('2', plain,
% 0.39/0.63      (![X20 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ X20)
% 0.39/0.63          | ~ (v1_funct_1 @ X20)
% 0.39/0.63          | ((X20) = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ X20 @ (k1_relat_1 @ X20)) @ 
% 0.39/0.63             (k1_relat_1 @ X20)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.63  thf('3', plain,
% 0.39/0.63      (((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.39/0.63         (k1_relat_1 @ sk_B))
% 0.39/0.63        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.39/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['0', '2'])).
% 0.39/0.63  thf('4', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('5', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('8', plain,
% 0.39/0.63      (((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.39/0.63         (k2_relat_1 @ sk_A))
% 0.39/0.63        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.39/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.39/0.63  thf('9', plain, (((sk_B) != (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('10', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('11', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.39/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.63  thf('12', plain,
% 0.39/0.63      ((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.39/0.63      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.39/0.63  thf('13', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(d4_funct_1, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.63       ( ![B:$i,C:$i]:
% 0.39/0.63         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.39/0.63             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.39/0.63               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.63           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.39/0.63             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.39/0.63               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.39/0.63          | (r2_hidden @ (k4_tarski @ X8 @ X11) @ X9)
% 0.39/0.63          | ((X11) != (k1_funct_1 @ X9 @ X8))
% 0.39/0.63          | ~ (v1_funct_1 @ X9)
% 0.39/0.63          | ~ (v1_relat_1 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.39/0.63  thf('15', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ X9)
% 0.39/0.63          | ~ (v1_funct_1 @ X9)
% 0.39/0.63          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.39/0.63          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.63  thf('16', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.39/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_B @ X0)) @ sk_B)
% 0.39/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.63          | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.63      inference('sup-', [status(thm)], ['13', '15'])).
% 0.39/0.63  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('19', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.39/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_B @ X0)) @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.39/0.63  thf('20', plain,
% 0.39/0.63      ((r2_hidden @ 
% 0.39/0.63        (k4_tarski @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.39/0.63         (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))) @ 
% 0.39/0.63        sk_B)),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '19'])).
% 0.39/0.63  thf('21', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.63         ((r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.39/0.63          | ((X10) = (k1_xboole_0))
% 0.39/0.63          | ((X10) != (k1_funct_1 @ X9 @ X8))
% 0.39/0.63          | ~ (v1_funct_1 @ X9)
% 0.39/0.63          | ~ (v1_relat_1 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.39/0.63  thf('22', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ X9)
% 0.39/0.63          | ~ (v1_funct_1 @ X9)
% 0.39/0.63          | ((k1_funct_1 @ X9 @ X8) = (k1_xboole_0))
% 0.39/0.63          | (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.63  thf('23', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ X9)
% 0.39/0.63          | ~ (v1_funct_1 @ X9)
% 0.39/0.63          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.39/0.63          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.63  thf('24', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.39/0.63          | ~ (v1_funct_1 @ X0)
% 0.39/0.63          | ~ (v1_relat_1 @ X0)
% 0.39/0.63          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.39/0.63          | ~ (v1_funct_1 @ X0)
% 0.39/0.63          | ~ (v1_relat_1 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.63  thf('25', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.39/0.63          | ~ (v1_relat_1 @ X0)
% 0.39/0.63          | ~ (v1_funct_1 @ X0)
% 0.39/0.63          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.63  thf('26', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('27', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ X9)
% 0.39/0.63          | ~ (v1_funct_1 @ X9)
% 0.39/0.63          | ((k1_funct_1 @ X9 @ X8) = (k1_xboole_0))
% 0.39/0.63          | (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.63  thf('28', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.39/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.39/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.63          | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['26', '27'])).
% 0.39/0.63  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('31', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.39/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.39/0.63      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.39/0.63  thf(d5_funct_1, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.63       ( ![B:$i]:
% 0.39/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.39/0.63           ( ![C:$i]:
% 0.39/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.63               ( ?[D:$i]:
% 0.39/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.39/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.63  thf('32', plain,
% 0.39/0.63      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.39/0.63         (((X15) != (k2_relat_1 @ X13))
% 0.39/0.63          | ((X16) = (k1_funct_1 @ X13 @ (sk_D_2 @ X16 @ X13)))
% 0.39/0.63          | ~ (r2_hidden @ X16 @ X15)
% 0.39/0.63          | ~ (v1_funct_1 @ X13)
% 0.46/0.63          | ~ (v1_relat_1 @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X13 : $i, X16 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X13)
% 0.46/0.63          | ~ (v1_funct_1 @ X13)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.46/0.63          | ((X16) = (k1_funct_1 @ X13 @ (sk_D_2 @ X16 @ X13))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | ((X0) = (k1_funct_1 @ sk_A @ (sk_D_2 @ X0 @ sk_A)))
% 0.46/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63          | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['31', '33'])).
% 0.46/0.63  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | ((X0) = (k1_funct_1 @ sk_A @ (sk_D_2 @ X0 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.46/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.46/0.63         (((X15) != (k2_relat_1 @ X13))
% 0.46/0.63          | (r2_hidden @ (sk_D_2 @ X16 @ X13) @ (k1_relat_1 @ X13))
% 0.46/0.63          | ~ (r2_hidden @ X16 @ X15)
% 0.46/0.63          | ~ (v1_funct_1 @ X13)
% 0.46/0.63          | ~ (v1_relat_1 @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X13 : $i, X16 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X13)
% 0.46/0.63          | ~ (v1_funct_1 @ X13)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.46/0.63          | (r2_hidden @ (sk_D_2 @ X16 @ X13) @ (k1_relat_1 @ X13)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ (sk_D_2 @ X0 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.46/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63          | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['38', '40'])).
% 0.46/0.63  thf('42', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ (sk_D_2 @ X0 @ sk_A) @ (k1_relat_1 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X8 : $i, X9 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X9)
% 0.46/0.63          | ~ (v1_funct_1 @ X9)
% 0.46/0.63          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.46/0.63          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ 
% 0.46/0.63              (k1_funct_1 @ sk_A @ (sk_D_2 @ X0 @ sk_A))) @ 
% 0.46/0.63             sk_A)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63          | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.63  thf('47', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ 
% 0.46/0.63              (k1_funct_1 @ sk_A @ (sk_D_2 @ X0 @ sk_A))) @ 
% 0.46/0.63             sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ X0) @ sk_A)
% 0.46/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['37', '49'])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ X0) @ sk_A))),
% 0.46/0.63      inference('simplify', [status(thm)], ['50'])).
% 0.46/0.63  thf('52', plain, (((k5_relat_1 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d8_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( v1_relat_1 @ B ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( v1_relat_1 @ C ) =>
% 0.46/0.63               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.46/0.63                 ( ![D:$i,E:$i]:
% 0.46/0.63                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.46/0.63                     ( ?[F:$i]:
% 0.46/0.63                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.46/0.63                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((X2) != (k5_relat_1 @ X1 @ X0))
% 0.46/0.63          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X2)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.46/0.63          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ sk_A)
% 0.46/0.63          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.63          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ sk_B)
% 0.46/0.63          | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['52', '54'])).
% 0.46/0.63  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('58', plain, (((k5_relat_1 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ sk_B)
% 0.46/0.63          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ X1) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['51', '60'])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.63          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.63          | (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ (k1_funct_1 @ sk_B @ X0)) @ 
% 0.46/0.63             sk_A)
% 0.46/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['25', '61'])).
% 0.46/0.63  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ (k1_funct_1 @ sk_B @ X0)) @ 
% 0.46/0.63             sk_A)
% 0.46/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ 
% 0.46/0.63           (k4_tarski @ (sk_D_2 @ X0 @ sk_A) @ (k1_funct_1 @ sk_B @ X0)) @ sk_A)
% 0.46/0.63          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      ((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X13 : $i, X16 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X13)
% 0.46/0.63          | ~ (v1_funct_1 @ X13)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.46/0.63          | (r2_hidden @ (sk_D_2 @ X16 @ X13) @ (k1_relat_1 @ X13)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      (((r2_hidden @ (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63         (k1_relat_1 @ sk_A))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('70', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      ((r2_hidden @ (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63        (k1_relat_1 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.46/0.63          | ((X11) = (k1_funct_1 @ X9 @ X8))
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ X9)
% 0.46/0.63          | ~ (v1_funct_1 @ X9)
% 0.46/0.63          | ~ (v1_relat_1 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ sk_A)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ 
% 0.46/0.63               (k4_tarski @ 
% 0.46/0.63                (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ X0) @ 
% 0.46/0.63               sk_A)
% 0.46/0.63          | ((X0)
% 0.46/0.63              = (k1_funct_1 @ sk_A @ 
% 0.46/0.63                 (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.63  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('76', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('77', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ 
% 0.46/0.63              (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ X0) @ 
% 0.46/0.63             sk_A)
% 0.46/0.63          | ((X0)
% 0.46/0.63              = (k1_funct_1 @ sk_A @ 
% 0.46/0.63                 (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.46/0.63  thf('78', plain,
% 0.46/0.63      ((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      (![X13 : $i, X16 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X13)
% 0.46/0.63          | ~ (v1_funct_1 @ X13)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.46/0.63          | ((X16) = (k1_funct_1 @ X13 @ (sk_D_2 @ X16 @ X13))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      ((((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.63          = (k1_funct_1 @ sk_A @ 
% 0.46/0.63             (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.63  thf('81', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.63         = (k1_funct_1 @ sk_A @ 
% 0.46/0.63            (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.46/0.63  thf('84', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ 
% 0.46/0.63              (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ X0) @ 
% 0.46/0.63             sk_A)
% 0.46/0.63          | ((X0) = (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['77', '83'])).
% 0.46/0.63  thf('85', plain,
% 0.46/0.63      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63          = (k1_xboole_0))
% 0.46/0.63        | ((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63            = (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['66', '84'])).
% 0.46/0.63  thf('86', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('87', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i]:
% 0.46/0.63         (((k1_relat_1 @ X20) != (X19))
% 0.46/0.63          | ((k1_funct_1 @ X20 @ (sk_C_1 @ X20 @ X19)) != (sk_C_1 @ X20 @ X19))
% 0.46/0.63          | ((X20) = (k6_relat_1 @ X19))
% 0.46/0.63          | ~ (v1_funct_1 @ X20)
% 0.46/0.63          | ~ (v1_relat_1 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.46/0.63  thf('88', plain,
% 0.46/0.63      (![X20 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X20)
% 0.46/0.63          | ~ (v1_funct_1 @ X20)
% 0.46/0.63          | ((X20) = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 0.46/0.63          | ((k1_funct_1 @ X20 @ (sk_C_1 @ X20 @ (k1_relat_1 @ X20)))
% 0.46/0.63              != (sk_C_1 @ X20 @ (k1_relat_1 @ X20))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['87'])).
% 0.46/0.63  thf('89', plain,
% 0.46/0.63      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63          != (sk_C_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.46/0.63        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['86', '88'])).
% 0.46/0.63  thf('90', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('91', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('92', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('93', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('94', plain,
% 0.46/0.63      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63          != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.46/0.63  thf('95', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.63  thf('96', plain,
% 0.46/0.63      (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63         != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 0.46/0.63  thf('97', plain,
% 0.46/0.63      (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63         = (k1_xboole_0))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['85', '96'])).
% 0.46/0.63  thf('98', plain,
% 0.46/0.63      ((r2_hidden @ 
% 0.46/0.63        (k4_tarski @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ k1_xboole_0) @ 
% 0.46/0.63        sk_B)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '97'])).
% 0.46/0.63  thf('99', plain,
% 0.46/0.63      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.63         = (k1_funct_1 @ sk_A @ 
% 0.46/0.63            (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.46/0.63  thf('100', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.63  thf('101', plain,
% 0.46/0.63      (((r2_hidden @ 
% 0.46/0.63         (k4_tarski @ 
% 0.46/0.63          (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63          (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.46/0.63         sk_A)
% 0.46/0.63        | ((k1_funct_1 @ sk_A @ 
% 0.46/0.63            (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.46/0.63            = (k1_xboole_0))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['99', '100'])).
% 0.46/0.63  thf('102', plain,
% 0.46/0.63      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.63         = (k1_funct_1 @ sk_A @ 
% 0.46/0.63            (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.46/0.63  thf('103', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('104', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('105', plain,
% 0.46/0.63      (((r2_hidden @ 
% 0.46/0.63         (k4_tarski @ 
% 0.46/0.63          (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63          (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.46/0.63         sk_A)
% 0.46/0.63        | ((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.46/0.63  thf('106', plain,
% 0.46/0.63      (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63         != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 0.46/0.63  thf('107', plain,
% 0.46/0.63      (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.63         = (k1_xboole_0))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['85', '96'])).
% 0.46/0.63  thf('108', plain, (((k1_xboole_0) != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.63  thf('109', plain,
% 0.46/0.63      ((r2_hidden @ 
% 0.46/0.63        (k4_tarski @ (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63         (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.46/0.63        sk_A)),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['105', '108'])).
% 0.46/0.63  thf('110', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ sk_A)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.46/0.63  thf('111', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ X0) @ sk_B)
% 0.46/0.63          | (r2_hidden @ 
% 0.46/0.63             (k4_tarski @ 
% 0.46/0.63              (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ X0) @ 
% 0.46/0.63             sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['109', '110'])).
% 0.46/0.63  thf('112', plain,
% 0.46/0.63      ((r2_hidden @ 
% 0.46/0.63        (k4_tarski @ (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63         k1_xboole_0) @ 
% 0.46/0.63        sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['98', '111'])).
% 0.46/0.63  thf('113', plain,
% 0.46/0.63      (![X8 : $i, X9 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X9)
% 0.46/0.63          | ~ (v1_funct_1 @ X9)
% 0.46/0.63          | ((k1_funct_1 @ X9 @ X8) = (k1_xboole_0))
% 0.46/0.63          | (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.63  thf('114', plain,
% 0.46/0.63      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.46/0.63          | ((X11) = (k1_funct_1 @ X9 @ X8))
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ X9)
% 0.46/0.63          | ~ (v1_funct_1 @ X9)
% 0.46/0.63          | ~ (v1_relat_1 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.63  thf('115', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.46/0.63          | ((X2) = (k1_funct_1 @ X0 @ X1)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['113', '114'])).
% 0.46/0.63  thf('116', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (((X2) = (k1_funct_1 @ X0 @ X1))
% 0.46/0.63          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['115'])).
% 0.46/0.63  thf('117', plain,
% 0.46/0.63      ((((k1_funct_1 @ sk_A @ 
% 0.46/0.63          (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.46/0.63          = (k1_xboole_0))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_A)
% 0.46/0.63        | ((k1_xboole_0)
% 0.46/0.63            = (k1_funct_1 @ sk_A @ 
% 0.46/0.63               (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['112', '116'])).
% 0.46/0.63  thf('118', plain,
% 0.46/0.63      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.63         = (k1_funct_1 @ sk_A @ 
% 0.46/0.63            (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.46/0.63  thf('119', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('120', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('121', plain,
% 0.46/0.63      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.63         = (k1_funct_1 @ sk_A @ 
% 0.46/0.63            (sk_D_2 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.46/0.63  thf('122', plain,
% 0.46/0.63      ((((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))
% 0.46/0.63        | ((k1_xboole_0) = (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 0.46/0.63  thf('123', plain, (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['122'])).
% 0.46/0.63  thf('124', plain, (((k1_xboole_0) != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.63  thf('125', plain, ($false),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['123', '124'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
