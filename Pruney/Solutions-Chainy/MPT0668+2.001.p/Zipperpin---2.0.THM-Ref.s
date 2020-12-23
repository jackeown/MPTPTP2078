%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ebxEeMMlmf

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:55 EST 2020

% Result     : Theorem 4.78s
% Output     : Refutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  281 (1071 expanded)
%              Number of leaves         :   24 ( 288 expanded)
%              Depth                    :   30
%              Number of atoms          : 4527 (21799 expanded)
%              Number of equality atoms :  220 ( 959 expanded)
%              Maximal formula depth    :   24 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t85_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_relat_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_relat_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) )
              & ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [D: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
       => ( ( k1_funct_1 @ B @ D )
          = ( k1_funct_1 @ C @ D ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( X8
       != ( k1_funct_1 @ X7 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( k1_funct_1 @ X7 @ X6 ) ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
        & ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( zip_tseitin_1 @ D @ C @ A ) )
              & ! [D: $i] :
                  ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( B
                = ( k8_relat_1 @ A @ C ) )
            <=> ( ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                  <=> ( zip_tseitin_1 @ D @ C @ A ) )
                & ! [D: $i] :
                    ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[zf_stmt_4])).

thf('4',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
      | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) )
        | ( r2_hidden @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( zip_tseitin_0 @ X0 @ X1 @ sk_B )
        | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ sk_A ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 @ sk_B )
        | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ sk_A ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_1 @ X13 @ X14 @ X16 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ X16 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X0 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_1 @ X0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 @ sk_B ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
    | ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
    | ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_relat_1 @ sk_B ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( k1_funct_1 @ X7 @ X6 ) ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('27',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_D_1 ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_D_1 ) ) @ sk_B )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_D_1 ) ) @ sk_C )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( X8
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k1_funct_1 @ sk_B @ sk_D_1 )
        = ( k1_funct_1 @ sk_C @ sk_D_1 ) ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D_1 )
      = ( k1_funct_1 @ sk_C @ sk_D_1 ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X11 @ X12 )
      | ( ( k1_funct_1 @ X12 @ X9 )
       != ( k1_funct_1 @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ X0 @ sk_D_1 )
         != ( k1_funct_1 @ sk_B @ sk_D_1 ) )
        | ( zip_tseitin_0 @ sk_D_1 @ sk_C @ X0 ) )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
   <= ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
      & ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('49',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
    | ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('51',plain,(
    ! [X18: $i] :
      ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( X8
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( X8
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X2 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X19: $i] :
      ( ( zip_tseitin_0 @ X19 @ sk_C @ sk_B )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B )
   <= ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('63',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( X8
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_E @ X2 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_1 @ X13 @ X14 @ X16 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ X16 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X3 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X3 )
      | ( zip_tseitin_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X3 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ( X0
          = ( k8_relat_1 @ sk_A @ sk_C ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_C )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k8_relat_1 @ sk_A @ sk_C ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_relat_1 @ X0 ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['87'])).

thf('89',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_funct_1 @ X10 @ X9 )
        = ( k1_funct_1 @ X11 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k8_relat_1 @ sk_A @ sk_C ) )
        | ~ ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ X0 @ sk_B )
        | ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
          = ( k1_funct_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        = ( k1_funct_1 @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','93'])).

thf('95',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        = ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('98',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('100',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        = ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        = ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        = ( k1_funct_1 @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','93'])).

thf('103',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('104',plain,
    ( ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
   <= ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('105',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( zip_tseitin_1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_C @ sk_A ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('107',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( k1_funct_1 @ X7 @ X6 ) ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('109',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('112',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) @ sk_C ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) @ sk_C )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['102','112'])).

thf('114',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) @ sk_C ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['101','114'])).

thf('116',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        = ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('118',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('119',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( k1_funct_1 @ X7 @ X6 ) ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('120',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('123',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) @ sk_B ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['117','123'])).

thf('125',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('127',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('129',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('130',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ sk_A ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( ~ ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ sk_A ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','131'])).

thf('133',plain,
    ( ( ~ ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ sk_A )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        = ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('135',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) @ sk_B ) )
   <= ! [X18: $i] :
        ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
        | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( X8
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_E @ X0 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_E @ X0 @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B )
   <= ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['60'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('144',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_funct_1 @ X10 @ X9 )
        = ( k1_funct_1 @ X11 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X0 @ X0 @ X1 ) @ X2 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X2 @ ( sk_D @ X0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_B @ X0 ) )
          = ( k1_funct_1 @ sk_C @ ( sk_D @ sk_B @ sk_B @ X0 ) ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['142','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('151',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_B @ X0 ) )
          = ( k1_funct_1 @ sk_C @ ( sk_D @ sk_B @ sk_B @ X0 ) ) )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) ) )
   <= ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('154',plain,
    ( ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
   <= ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ( zip_tseitin_1 @ ( sk_D @ sk_B @ sk_B @ X0 ) @ sk_C @ sk_A ) )
   <= ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('157',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('158',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ( zip_tseitin_1 @ ( sk_D @ sk_B @ sk_B @ X0 ) @ sk_C @ sk_A ) )
   <= ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ X15 )
      | ~ ( zip_tseitin_1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_B @ sk_B @ X0 ) ) @ sk_A ) )
   <= ! [X17: $i] :
        ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
        | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_B @ X0 ) ) @ sk_A )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['152','160'])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_B @ X0 ) ) @ sk_A ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_E @ sk_B @ sk_B @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('165',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_E @ sk_B @ sk_B @ X0 ) @ sk_A )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k8_relat_1 @ X0 @ sk_B ) )
        | ( r2_hidden @ ( sk_E @ sk_B @ sk_B @ X0 ) @ sk_A ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['168','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('177',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_B ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_B ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('180',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_B ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('182',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('183',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('184',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ( r2_hidden @ X0 @ sk_A ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ sk_A ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','184'])).

thf('186',plain,
    ( ( ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ sk_A )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','185'])).

thf('187',plain,
    ( ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ sk_A ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['133','187'])).

thf('189',plain,
    ( ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('190',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      & ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) )
      & ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
      & ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ! [X18: $i] :
          ( ~ ( zip_tseitin_1 @ X18 @ sk_C @ sk_A )
          | ( r2_hidden @ X18 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B )
    | ~ ! [X17: $i] :
          ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_B ) )
          | ( zip_tseitin_1 @ X17 @ sk_C @ sk_A ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B )
   <= ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['60'])).

thf('193',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
   <= ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('194',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ! [X19: $i] :
          ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
    | ! [X19: $i] :
        ( zip_tseitin_0 @ X19 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['60'])).

thf('196',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
    | ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('197',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['196'])).

thf('198',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
   <= ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('199',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('200',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C ) )
   <= ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( k1_funct_1 @ X7 @ X6 ) ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('202',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_C @ sk_D_2 ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('205',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_C @ sk_D_2 ) ) @ sk_C )
   <= ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('207',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('208',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k8_relat_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('211',plain,
    ( ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('213',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,
    ( ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_D_2 ) @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_C @ sk_D_2 ) ) @ sk_B ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['205','213'])).

thf('215',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
   <= ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('216',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ X15 )
      | ~ ( zip_tseitin_1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('217',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_D_2 ) @ sk_A )
   <= ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_C @ sk_D_2 ) ) @ sk_B )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','217'])).

thf('219',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('220',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('222',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('223',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['196'])).

thf('225',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
    | ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('227',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('228',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( k1_funct_1 @ X7 @ X6 ) ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('229',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_B @ sk_D_2 ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('231',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('232',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_B @ sk_D_2 ) ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('234',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_D_2 ) @ sk_A )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_B @ sk_D_2 ) ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('236',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C ) )
   <= ( sk_B
      = ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('237',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_B @ sk_D_2 ) ) @ sk_C )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( X8
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('239',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k1_funct_1 @ sk_B @ sk_D_2 )
        = ( k1_funct_1 @ sk_C @ sk_D_2 ) ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('242',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D_2 )
      = ( k1_funct_1 @ sk_C @ sk_D_2 ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_1 @ X13 @ X14 @ X16 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ X16 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('244',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_D_2 ) @ X0 )
        | ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_1 @ sk_D_2 @ sk_C @ X0 ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( k1_funct_1 @ sk_B @ sk_D_2 ) ) @ sk_C )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('246',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X7 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('247',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('249',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('250',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_D_2 ) @ X0 )
        | ( zip_tseitin_1 @ sk_D_2 @ sk_C @ X0 ) )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['244','250'])).

thf('252',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
   <= ( ( sk_B
        = ( k8_relat_1 @ sk_A @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['234','251'])).

thf('253',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
   <= ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['196'])).

thf('254',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A )
    | ( sk_B
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['49','50','52','191','194','195','197','225','226','254'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ebxEeMMlmf
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.78/5.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.78/5.03  % Solved by: fo/fo7.sh
% 4.78/5.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.78/5.03  % done 4106 iterations in 4.528s
% 4.78/5.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.78/5.03  % SZS output start Refutation
% 4.78/5.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.78/5.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.78/5.03  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 4.78/5.03  thf(sk_C_type, type, sk_C: $i).
% 4.78/5.03  thf(sk_A_type, type, sk_A: $i).
% 4.78/5.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.78/5.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.78/5.03  thf(sk_D_2_type, type, sk_D_2: $i).
% 4.78/5.03  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.78/5.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 4.78/5.03  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 4.78/5.03  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.78/5.03  thf(sk_B_type, type, sk_B: $i).
% 4.78/5.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.78/5.03  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.78/5.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.78/5.03  thf(t85_funct_1, conjecture,
% 4.78/5.03    (![A:$i,B:$i]:
% 4.78/5.03     ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 4.78/5.03       ( ![C:$i]:
% 4.78/5.03         ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 4.78/5.03           ( ( ( B ) = ( k8_relat_1 @ A @ C ) ) <=>
% 4.78/5.03             ( ( ![D:$i]:
% 4.78/5.03                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 4.78/5.03                   ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) & 
% 4.78/5.03               ( ![D:$i]:
% 4.78/5.03                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) <=>
% 4.78/5.03                   ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) & 
% 4.78/5.03                     ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) ) ))).
% 4.78/5.03  thf(zf_stmt_0, axiom,
% 4.78/5.03    (![D:$i,C:$i,B:$i]:
% 4.78/5.03     ( ( zip_tseitin_0 @ D @ C @ B ) <=>
% 4.78/5.03       ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 4.78/5.03         ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ))).
% 4.78/5.03  thf('0', plain,
% 4.78/5.03      (![X9 : $i, X11 : $i, X12 : $i]:
% 4.78/5.03         ((zip_tseitin_0 @ X9 @ X11 @ X12)
% 4.78/5.03          | (r2_hidden @ X9 @ (k1_relat_1 @ X12)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf(t8_funct_1, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i]:
% 4.78/5.03     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.78/5.03       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 4.78/5.03         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 4.78/5.03           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 4.78/5.03  thf('1', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 4.78/5.03          | ((X8) != (k1_funct_1 @ X7 @ X6))
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('2', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X7)
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X6 @ (k1_funct_1 @ X7 @ X6)) @ X7)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['1'])).
% 4.78/5.03  thf('3', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         ((zip_tseitin_0 @ X1 @ X2 @ X0)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['0', '2'])).
% 4.78/5.03  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.78/5.03  thf(zf_stmt_2, axiom,
% 4.78/5.03    (![D:$i,C:$i,A:$i]:
% 4.78/5.03     ( ( zip_tseitin_1 @ D @ C @ A ) <=>
% 4.78/5.03       ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) & 
% 4.78/5.03         ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ))).
% 4.78/5.03  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 4.78/5.03  thf(zf_stmt_4, conjecture,
% 4.78/5.03    (![A:$i,B:$i]:
% 4.78/5.03     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.78/5.03       ( ![C:$i]:
% 4.78/5.03         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.78/5.03           ( ( ( B ) = ( k8_relat_1 @ A @ C ) ) <=>
% 4.78/5.03             ( ( ![D:$i]:
% 4.78/5.03                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) <=>
% 4.78/5.03                   ( zip_tseitin_1 @ D @ C @ A ) ) ) & 
% 4.78/5.03               ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) ) ))).
% 4.78/5.03  thf(zf_stmt_5, negated_conjecture,
% 4.78/5.03    (~( ![A:$i,B:$i]:
% 4.78/5.03        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.78/5.03          ( ![C:$i]:
% 4.78/5.03            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.78/5.03              ( ( ( B ) = ( k8_relat_1 @ A @ C ) ) <=>
% 4.78/5.03                ( ( ![D:$i]:
% 4.78/5.03                    ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) <=>
% 4.78/5.03                      ( zip_tseitin_1 @ D @ C @ A ) ) ) & 
% 4.78/5.03                  ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) ) ) )),
% 4.78/5.03    inference('cnf.neg', [status(esa)], [zf_stmt_4])).
% 4.78/5.03  thf('4', plain,
% 4.78/5.03      (![X17 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03          | (zip_tseitin_1 @ X17 @ sk_C @ sk_A)
% 4.78/5.03          | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('5', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf(d12_relat_1, axiom,
% 4.78/5.03    (![A:$i,B:$i]:
% 4.78/5.03     ( ( v1_relat_1 @ B ) =>
% 4.78/5.03       ( ![C:$i]:
% 4.78/5.03         ( ( v1_relat_1 @ C ) =>
% 4.78/5.03           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 4.78/5.03             ( ![D:$i,E:$i]:
% 4.78/5.03               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 4.78/5.03                 ( ( r2_hidden @ E @ A ) & 
% 4.78/5.03                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 4.78/5.03  thf('6', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ X5 @ X1)
% 4.78/5.03          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('7', plain,
% 4.78/5.03      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ X5 @ X1)
% 4.78/5.03          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['6'])).
% 4.78/5.03  thf('8', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03           | (r2_hidden @ X0 @ sk_A)
% 4.78/5.03           | ~ (v1_relat_1 @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['5', '7'])).
% 4.78/5.03  thf('9', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('12', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | (r2_hidden @ X0 @ sk_A)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 4.78/5.03  thf('13', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (v1_relat_1 @ sk_B)
% 4.78/5.03           | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03           | (zip_tseitin_0 @ X0 @ X1 @ sk_B)
% 4.78/5.03           | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ sk_A)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['3', '12'])).
% 4.78/5.03  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('16', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          ((zip_tseitin_0 @ X0 @ X1 @ sk_B)
% 4.78/5.03           | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ sk_A)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['13', '14', '15'])).
% 4.78/5.03  thf('17', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X16 : $i]:
% 4.78/5.03         ((zip_tseitin_1 @ X13 @ X14 @ X16)
% 4.78/5.03          | ~ (r2_hidden @ (k1_funct_1 @ X14 @ X13) @ X16)
% 4.78/5.03          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X14)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('18', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          ((zip_tseitin_0 @ X0 @ X1 @ sk_B)
% 4.78/5.03           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 4.78/5.03           | (zip_tseitin_1 @ X0 @ sk_B @ sk_A)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['16', '17'])).
% 4.78/5.03  thf('19', plain,
% 4.78/5.03      (![X9 : $i, X11 : $i, X12 : $i]:
% 4.78/5.03         ((zip_tseitin_0 @ X9 @ X11 @ X12)
% 4.78/5.03          | (r2_hidden @ X9 @ (k1_relat_1 @ X12)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('20', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          ((zip_tseitin_1 @ X0 @ sk_B @ sk_A)
% 4.78/5.03           | (zip_tseitin_0 @ X0 @ X1 @ sk_B)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('clc', [status(thm)], ['18', '19'])).
% 4.78/5.03  thf('21', plain,
% 4.78/5.03      ((~ (zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)
% 4.78/5.03        | (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))
% 4.78/5.03        | (zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)
% 4.78/5.03        | ((sk_B) != (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('22', plain,
% 4.78/5.03      ((~ (zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('23', plain,
% 4.78/5.03      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['20', '22'])).
% 4.78/5.03  thf('24', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.78/5.03         ((r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 4.78/5.03          | ~ (zip_tseitin_1 @ X13 @ X14 @ X15))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('25', plain,
% 4.78/5.03      (((r2_hidden @ sk_D_1 @ (k1_relat_1 @ sk_B)))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['23', '24'])).
% 4.78/5.03  thf('26', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X7)
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X6 @ (k1_funct_1 @ X7 @ X6)) @ X7)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['1'])).
% 4.78/5.03  thf('27', plain,
% 4.78/5.03      ((((r2_hidden @ (k4_tarski @ sk_D_1 @ (k1_funct_1 @ sk_B @ sk_D_1)) @ 
% 4.78/5.03          sk_B)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03         | ~ (v1_relat_1 @ sk_B)))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['25', '26'])).
% 4.78/5.03  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('30', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_1 @ (k1_funct_1 @ sk_B @ sk_D_1)) @ sk_B))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['27', '28', '29'])).
% 4.78/5.03  thf('31', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('32', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 4.78/5.03          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('33', plain,
% 4.78/5.03      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['32'])).
% 4.78/5.03  thf('34', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03           | (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)
% 4.78/5.03           | ~ (v1_relat_1 @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['31', '33'])).
% 4.78/5.03  thf('35', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('38', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 4.78/5.03  thf('39', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_1 @ (k1_funct_1 @ sk_B @ sk_D_1)) @ sk_C))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['30', '38'])).
% 4.78/5.03  thf('40', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | ((X8) = (k1_funct_1 @ X7 @ X6))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('41', plain,
% 4.78/5.03      (((~ (v1_relat_1 @ sk_C)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_C)
% 4.78/5.03         | ((k1_funct_1 @ sk_B @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_D_1))))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['39', '40'])).
% 4.78/5.03  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('44', plain,
% 4.78/5.03      ((((k1_funct_1 @ sk_B @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_D_1)))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['41', '42', '43'])).
% 4.78/5.03  thf('45', plain,
% 4.78/5.03      (![X9 : $i, X11 : $i, X12 : $i]:
% 4.78/5.03         ((zip_tseitin_0 @ X9 @ X11 @ X12)
% 4.78/5.03          | ((k1_funct_1 @ X12 @ X9) != (k1_funct_1 @ X11 @ X9)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('46', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((k1_funct_1 @ X0 @ sk_D_1) != (k1_funct_1 @ sk_B @ sk_D_1))
% 4.78/5.03           | (zip_tseitin_0 @ sk_D_1 @ sk_C @ X0)))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['44', '45'])).
% 4.78/5.03  thf('47', plain,
% 4.78/5.03      (((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) & 
% 4.78/5.03             (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('eq_res', [status(thm)], ['46'])).
% 4.78/5.03  thf('48', plain,
% 4.78/5.03      ((~ (zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('49', plain,
% 4.78/5.03      (((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) | 
% 4.78/5.03       ~ (((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['47', '48'])).
% 4.78/5.03  thf('50', plain,
% 4.78/5.03      ((![X17 : $i]:
% 4.78/5.03          (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03           | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) | 
% 4.78/5.03       (((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('51', plain,
% 4.78/5.03      (![X18 : $i]:
% 4.78/5.03         (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03          | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B))
% 4.78/5.03          | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('52', plain,
% 4.78/5.03      ((![X18 : $i]:
% 4.78/5.03          (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03           | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) | 
% 4.78/5.03       (((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('split', [status(esa)], ['51'])).
% 4.78/5.03  thf('53', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('54', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | ((X8) = (k1_funct_1 @ X7 @ X6))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('55', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((sk_E @ X0 @ X2 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X0 @ X2 @ X1))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['53', '54'])).
% 4.78/5.03  thf('56', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (((sk_E @ X0 @ X2 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X0 @ X2 @ X1)))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('simplify', [status(thm)], ['55'])).
% 4.78/5.03  thf('57', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | ((X8) = (k1_funct_1 @ X7 @ X6))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('58', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | ((sk_E @ X2 @ X0 @ X1) = (k1_funct_1 @ X2 @ (sk_D @ X2 @ X0 @ X1)))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((sk_E @ X2 @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X2 @ X0 @ X1))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['56', '57'])).
% 4.78/5.03  thf('59', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (((sk_E @ X2 @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X2 @ X0 @ X1)))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((sk_E @ X2 @ X0 @ X1) = (k1_funct_1 @ X2 @ (sk_D @ X2 @ X0 @ X1)))
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['58'])).
% 4.78/5.03  thf('60', plain,
% 4.78/5.03      (![X19 : $i]:
% 4.78/5.03         ((zip_tseitin_0 @ X19 @ sk_C @ sk_B)
% 4.78/5.03          | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('61', plain,
% 4.78/5.03      ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B))
% 4.78/5.03         <= ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['60'])).
% 4.78/5.03  thf('62', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('63', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('64', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ (k1_relat_1 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['62', '63'])).
% 4.78/5.03  thf('65', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ (k1_relat_1 @ X0))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('simplify', [status(thm)], ['64'])).
% 4.78/5.03  thf('66', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('67', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('68', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ (k1_relat_1 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['66', '67'])).
% 4.78/5.03  thf('69', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ (k1_relat_1 @ X0))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('simplify', [status(thm)], ['68'])).
% 4.78/5.03  thf('70', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('71', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['69', '70'])).
% 4.78/5.03  thf('72', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['71'])).
% 4.78/5.03  thf('73', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ (k1_relat_1 @ X0))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('simplify', [status(thm)], ['68'])).
% 4.78/5.03  thf('74', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | ((X8) = (k1_funct_1 @ X7 @ X6))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('75', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((sk_E @ X2 @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X2 @ X0 @ X1))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['73', '74'])).
% 4.78/5.03  thf('76', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (((sk_E @ X2 @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X2 @ X0 @ X1)))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['75'])).
% 4.78/5.03  thf('77', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X16 : $i]:
% 4.78/5.03         ((zip_tseitin_1 @ X13 @ X14 @ X16)
% 4.78/5.03          | ~ (r2_hidden @ (k1_funct_1 @ X14 @ X13) @ X16)
% 4.78/5.03          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X14)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('78', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X3)
% 4.78/5.03          | ~ (v1_relat_1 @ X1)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X0 @ X1))
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X1)
% 4.78/5.03          | ~ (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k1_relat_1 @ X1))
% 4.78/5.03          | (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ X0) @ X1 @ X3))),
% 4.78/5.03      inference('sup-', [status(thm)], ['76', '77'])).
% 4.78/5.03  thf('79', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (zip_tseitin_1 @ (sk_D @ X2 @ X0 @ X1) @ X0 @ X3)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X3))),
% 4.78/5.03      inference('sup-', [status(thm)], ['72', '78'])).
% 4.78/5.03  thf('80', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X3)
% 4.78/5.03          | (zip_tseitin_1 @ (sk_D @ X2 @ X0 @ X1) @ X0 @ X3)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['79'])).
% 4.78/5.03  thf('81', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X1)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X0 @ X1))
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X1)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X0 @ X1))
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X1)
% 4.78/5.03          | (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ X0) @ X1 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['65', '80'])).
% 4.78/5.03  thf('82', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         ((zip_tseitin_1 @ (sk_D @ X2 @ X1 @ X0) @ X1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X1)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 4.78/5.03          | ~ (v1_funct_1 @ X2)
% 4.78/5.03          | ~ (v1_relat_1 @ X2)
% 4.78/5.03          | ((X2) = (k8_relat_1 @ X0 @ X1))
% 4.78/5.03          | ~ (v1_relat_1 @ X1))),
% 4.78/5.03      inference('simplify', [status(thm)], ['81'])).
% 4.78/5.03  thf('83', plain,
% 4.78/5.03      ((![X18 : $i]:
% 4.78/5.03          (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03           | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('split', [status(esa)], ['51'])).
% 4.78/5.03  thf('84', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (~ (v1_relat_1 @ sk_C)
% 4.78/5.03           | ((X0) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03           | ~ (v1_relat_1 @ X0)
% 4.78/5.03           | ~ (v1_funct_1 @ X0)
% 4.78/5.03           | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_A) @ (k1_relat_1 @ X0))
% 4.78/5.03           | ~ (v1_funct_1 @ sk_C)
% 4.78/5.03           | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['82', '83'])).
% 4.78/5.03  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('87', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((X0) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03           | ~ (v1_relat_1 @ X0)
% 4.78/5.03           | ~ (v1_funct_1 @ X0)
% 4.78/5.03           | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_A) @ (k1_relat_1 @ X0))
% 4.78/5.03           | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('demod', [status(thm)], ['84', '85', '86'])).
% 4.78/5.03  thf('88', plain,
% 4.78/5.03      ((((r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.78/5.03         | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03         | ~ (v1_relat_1 @ sk_B)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('eq_fact', [status(thm)], ['87'])).
% 4.78/5.03  thf('89', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('90', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('91', plain,
% 4.78/5.03      ((((r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('demod', [status(thm)], ['88', '89', '90'])).
% 4.78/5.03  thf('92', plain,
% 4.78/5.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 4.78/5.03          | ((k1_funct_1 @ X10 @ X9) = (k1_funct_1 @ X11 @ X9))
% 4.78/5.03          | ~ (zip_tseitin_0 @ X9 @ X11 @ X10))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('93', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03           | ~ (zip_tseitin_0 @ (sk_D @ sk_B @ sk_C @ sk_A) @ X0 @ sk_B)
% 4.78/5.03           | ((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03               = (k1_funct_1 @ X0 @ (sk_D @ sk_B @ sk_C @ sk_A)))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['91', '92'])).
% 4.78/5.03  thf('94', plain,
% 4.78/5.03      (((((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03           = (k1_funct_1 @ sk_C @ (sk_D @ sk_B @ sk_C @ sk_A)))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['61', '93'])).
% 4.78/5.03  thf('95', plain,
% 4.78/5.03      (((((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03           = (sk_E @ sk_B @ sk_C @ sk_A))
% 4.78/5.03         | ~ (v1_relat_1 @ sk_C)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ~ (v1_relat_1 @ sk_B)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03         | ((sk_E @ sk_B @ sk_C @ sk_A)
% 4.78/5.03             = (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A)))
% 4.78/5.03         | ~ (v1_funct_1 @ sk_C)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['59', '94'])).
% 4.78/5.03  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('98', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('100', plain,
% 4.78/5.03      (((((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03           = (sk_E @ sk_B @ sk_C @ sk_A))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((sk_E @ sk_B @ sk_C @ sk_A)
% 4.78/5.03             = (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A)))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 4.78/5.03  thf('101', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03             = (sk_E @ sk_B @ sk_C @ sk_A))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['100'])).
% 4.78/5.03  thf('102', plain,
% 4.78/5.03      (((((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03           = (k1_funct_1 @ sk_C @ (sk_D @ sk_B @ sk_C @ sk_A)))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['61', '93'])).
% 4.78/5.03  thf('103', plain,
% 4.78/5.03      ((((r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('demod', [status(thm)], ['88', '89', '90'])).
% 4.78/5.03  thf('104', plain,
% 4.78/5.03      ((![X17 : $i]:
% 4.78/5.03          (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03           | (zip_tseitin_1 @ X17 @ sk_C @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('105', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (zip_tseitin_1 @ (sk_D @ sk_B @ sk_C @ sk_A) @ sk_C @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['103', '104'])).
% 4.78/5.03  thf('106', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.78/5.03         ((r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 4.78/5.03          | ~ (zip_tseitin_1 @ X13 @ X14 @ X15))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('107', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ (k1_relat_1 @ sk_C))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['105', '106'])).
% 4.78/5.03  thf('108', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X7)
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X6 @ (k1_funct_1 @ X7 @ X6)) @ X7)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['1'])).
% 4.78/5.03  thf('109', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (k1_funct_1 @ sk_C @ (sk_D @ sk_B @ sk_C @ sk_A))) @ 
% 4.78/5.03            sk_C)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_C)
% 4.78/5.03         | ~ (v1_relat_1 @ sk_C)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['107', '108'])).
% 4.78/5.03  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('112', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (k1_funct_1 @ sk_C @ (sk_D @ sk_B @ sk_C @ sk_A))) @ 
% 4.78/5.03            sk_C)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('demod', [status(thm)], ['109', '110', '111'])).
% 4.78/5.03  thf('113', plain,
% 4.78/5.03      ((((r2_hidden @ 
% 4.78/5.03          (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03           (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))) @ 
% 4.78/5.03          sk_C)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['102', '112'])).
% 4.78/5.03  thf('114', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))) @ 
% 4.78/5.03            sk_C)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['113'])).
% 4.78/5.03  thf('115', plain,
% 4.78/5.03      ((((r2_hidden @ 
% 4.78/5.03          (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03           (sk_E @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03          sk_C)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['101', '114'])).
% 4.78/5.03  thf('116', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (sk_E @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03            sk_C)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['115'])).
% 4.78/5.03  thf('117', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03             = (sk_E @ sk_B @ sk_C @ sk_A))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['100'])).
% 4.78/5.03  thf('118', plain,
% 4.78/5.03      ((((r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('demod', [status(thm)], ['88', '89', '90'])).
% 4.78/5.03  thf('119', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X7)
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X6 @ (k1_funct_1 @ X7 @ X6)) @ X7)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['1'])).
% 4.78/5.03  thf('120', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))) @ 
% 4.78/5.03            sk_B)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03         | ~ (v1_relat_1 @ sk_B)))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['118', '119'])).
% 4.78/5.03  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('123', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))) @ 
% 4.78/5.03            sk_B)))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('demod', [status(thm)], ['120', '121', '122'])).
% 4.78/5.03  thf('124', plain,
% 4.78/5.03      ((((r2_hidden @ 
% 4.78/5.03          (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03           (sk_E @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03          sk_B)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['117', '123'])).
% 4.78/5.03  thf('125', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (sk_E @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03            sk_B)))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['124'])).
% 4.78/5.03  thf('126', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ 
% 4.78/5.03               (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 4.78/5.03          | ~ (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 4.78/5.03          | ~ (r2_hidden @ 
% 4.78/5.03               (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('127', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ~ (v1_relat_1 @ sk_C)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ~ (r2_hidden @ 
% 4.78/5.03              (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03               (sk_E @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03              sk_C)
% 4.78/5.03         | ~ (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A) @ sk_A)
% 4.78/5.03         | ~ (v1_relat_1 @ sk_B)))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['125', '126'])).
% 4.78/5.03  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('129', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('130', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ~ (r2_hidden @ 
% 4.78/5.03              (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03               (sk_E @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03              sk_C)
% 4.78/5.03         | ~ (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A) @ sk_A)))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['127', '128', '129'])).
% 4.78/5.03  thf('131', plain,
% 4.78/5.03      (((~ (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A) @ sk_A)
% 4.78/5.03         | ~ (r2_hidden @ 
% 4.78/5.03              (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03               (sk_E @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03              sk_C)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['130'])).
% 4.78/5.03  thf('132', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ~ (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A) @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['116', '131'])).
% 4.78/5.03  thf('133', plain,
% 4.78/5.03      (((~ (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A) @ sk_A)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['132'])).
% 4.78/5.03  thf('134', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))
% 4.78/5.03             = (sk_E @ sk_B @ sk_C @ sk_A))))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['100'])).
% 4.78/5.03  thf('135', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ 
% 4.78/5.03            (k4_tarski @ (sk_D @ sk_B @ sk_C @ sk_A) @ 
% 4.78/5.03             (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A))) @ 
% 4.78/5.03            sk_B)))
% 4.78/5.03         <= ((![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))))),
% 4.78/5.03      inference('demod', [status(thm)], ['120', '121', '122'])).
% 4.78/5.03  thf('136', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('137', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | (r2_hidden @ 
% 4.78/5.03             (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('eq_fact', [status(thm)], ['136'])).
% 4.78/5.03  thf('138', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ 
% 4.78/5.03           (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['137'])).
% 4.78/5.03  thf('139', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | ((X8) = (k1_funct_1 @ X7 @ X6))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('140', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((sk_E @ X0 @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X0 @ X0 @ X1))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['138', '139'])).
% 4.78/5.03  thf('141', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (((sk_E @ X0 @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_D @ X0 @ X0 @ X1)))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['140'])).
% 4.78/5.03  thf('142', plain,
% 4.78/5.03      ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B))
% 4.78/5.03         <= ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['60'])).
% 4.78/5.03  thf('143', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ 
% 4.78/5.03           (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['137'])).
% 4.78/5.03  thf('144', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('145', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['143', '144'])).
% 4.78/5.03  thf('146', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['145'])).
% 4.78/5.03  thf('147', plain,
% 4.78/5.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 4.78/5.03          | ((k1_funct_1 @ X10 @ X9) = (k1_funct_1 @ X11 @ X9))
% 4.78/5.03          | ~ (zip_tseitin_0 @ X9 @ X11 @ X10))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('148', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ~ (zip_tseitin_0 @ (sk_D @ X0 @ X0 @ X1) @ X2 @ X0)
% 4.78/5.03          | ((k1_funct_1 @ X0 @ (sk_D @ X0 @ X0 @ X1))
% 4.78/5.03              = (k1_funct_1 @ X2 @ (sk_D @ X0 @ X0 @ X1))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['146', '147'])).
% 4.78/5.03  thf('149', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_B @ X0))
% 4.78/5.03             = (k1_funct_1 @ sk_C @ (sk_D @ sk_B @ sk_B @ X0)))
% 4.78/5.03           | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | ~ (v1_relat_1 @ sk_B)))
% 4.78/5.03         <= ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['142', '148'])).
% 4.78/5.03  thf('150', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('151', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('152', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_B @ X0))
% 4.78/5.03             = (k1_funct_1 @ sk_C @ (sk_D @ sk_B @ sk_B @ X0)))
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))))
% 4.78/5.03         <= ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['149', '150', '151'])).
% 4.78/5.03  thf('153', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 4.78/5.03          | ~ (v1_funct_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['145'])).
% 4.78/5.03  thf('154', plain,
% 4.78/5.03      ((![X17 : $i]:
% 4.78/5.03          (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03           | (zip_tseitin_1 @ X17 @ sk_C @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('155', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (~ (v1_relat_1 @ sk_B)
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03           | (zip_tseitin_1 @ (sk_D @ sk_B @ sk_B @ X0) @ sk_C @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['153', '154'])).
% 4.78/5.03  thf('156', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('157', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('158', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | (zip_tseitin_1 @ (sk_D @ sk_B @ sk_B @ X0) @ sk_C @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))))),
% 4.78/5.03      inference('demod', [status(thm)], ['155', '156', '157'])).
% 4.78/5.03  thf('159', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.78/5.03         ((r2_hidden @ (k1_funct_1 @ X14 @ X13) @ X15)
% 4.78/5.03          | ~ (zip_tseitin_1 @ X13 @ X14 @ X15))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('160', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_D @ sk_B @ sk_B @ X0)) @ 
% 4.78/5.03              sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['158', '159'])).
% 4.78/5.03  thf('161', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          ((r2_hidden @ (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_B @ X0)) @ sk_A)
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['152', '160'])).
% 4.78/5.03  thf('162', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_B @ X0)) @ 
% 4.78/5.03              sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['161'])).
% 4.78/5.03  thf('163', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          ((r2_hidden @ (sk_E @ sk_B @ sk_B @ X0) @ sk_A)
% 4.78/5.03           | ~ (v1_relat_1 @ sk_B)
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['141', '162'])).
% 4.78/5.03  thf('164', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('165', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('166', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          ((r2_hidden @ (sk_E @ sk_B @ sk_B @ X0) @ sk_A)
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | ((sk_B) = (k8_relat_1 @ X0 @ sk_B))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['163', '164', '165'])).
% 4.78/5.03  thf('167', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((sk_B) = (k8_relat_1 @ X0 @ sk_B))
% 4.78/5.03           | (r2_hidden @ (sk_E @ sk_B @ sk_B @ X0) @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['166'])).
% 4.78/5.03  thf('168', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ 
% 4.78/5.03           (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['137'])).
% 4.78/5.03  thf('169', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ 
% 4.78/5.03           (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['137'])).
% 4.78/5.03  thf('170', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ 
% 4.78/5.03               (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X0)
% 4.78/5.03          | ~ (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 4.78/5.03          | ~ (r2_hidden @ 
% 4.78/5.03               (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('171', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (r2_hidden @ 
% 4.78/5.03               (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1)
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['169', '170'])).
% 4.78/5.03  thf('172', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1)
% 4.78/5.03          | ~ (r2_hidden @ 
% 4.78/5.03               (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_E @ X0 @ X0 @ X1)) @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['171'])).
% 4.78/5.03  thf('173', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['168', '172'])).
% 4.78/5.03  thf('174', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (sk_E @ X0 @ X0 @ X1) @ X1)
% 4.78/5.03          | ((X0) = (k8_relat_1 @ X1 @ X0))
% 4.78/5.03          | ~ (v1_relat_1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['173'])).
% 4.78/5.03  thf('175', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_B))
% 4.78/5.03         | ~ (v1_relat_1 @ sk_B)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_B))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['167', '174'])).
% 4.78/5.03  thf('176', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('177', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_B))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_B))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['175', '176'])).
% 4.78/5.03  thf('178', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_B)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['177'])).
% 4.78/5.03  thf('179', plain,
% 4.78/5.03      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ X5 @ X1)
% 4.78/5.03          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['6'])).
% 4.78/5.03  thf('180', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))
% 4.78/5.03           | (r2_hidden @ X0 @ sk_A)
% 4.78/5.03           | ~ (v1_relat_1 @ sk_B)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['178', '179'])).
% 4.78/5.03  thf('181', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_B)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['177'])).
% 4.78/5.03  thf('182', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('183', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('184', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | (r2_hidden @ X0 @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 4.78/5.03  thf('185', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_C @ sk_A)) @ 
% 4.78/5.03            sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['135', '184'])).
% 4.78/5.03  thf('186', plain,
% 4.78/5.03      ((((r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A) @ sk_A)
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | ((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['134', '185'])).
% 4.78/5.03  thf('187', plain,
% 4.78/5.03      (((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03         | (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A) @ sk_A)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['186'])).
% 4.78/5.03  thf('188', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= ((![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('clc', [status(thm)], ['133', '187'])).
% 4.78/5.03  thf('189', plain,
% 4.78/5.03      ((((sk_B) != (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= (~ (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('190', plain,
% 4.78/5.03      ((((sk_B) != (sk_B)))
% 4.78/5.03         <= (~ (((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             (![X17 : $i]:
% 4.78/5.03                (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03                 | (zip_tseitin_1 @ X17 @ sk_C @ sk_A))) & 
% 4.78/5.03             (![X18 : $i]:
% 4.78/5.03                (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03                 | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) & 
% 4.78/5.03             (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['188', '189'])).
% 4.78/5.03  thf('191', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) | 
% 4.78/5.03       ~
% 4.78/5.03       (![X18 : $i]:
% 4.78/5.03          (~ (zip_tseitin_1 @ X18 @ sk_C @ sk_A)
% 4.78/5.03           | (r2_hidden @ X18 @ (k1_relat_1 @ sk_B)))) | 
% 4.78/5.03       ~ (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)) | 
% 4.78/5.03       ~
% 4.78/5.03       (![X17 : $i]:
% 4.78/5.03          (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_B))
% 4.78/5.03           | (zip_tseitin_1 @ X17 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['190'])).
% 4.78/5.03  thf('192', plain,
% 4.78/5.03      ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B))
% 4.78/5.03         <= ((![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['60'])).
% 4.78/5.03  thf('193', plain,
% 4.78/5.03      ((~ (zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B))
% 4.78/5.03         <= (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('194', plain,
% 4.78/5.03      (((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) | 
% 4.78/5.03       ~ (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B))),
% 4.78/5.03      inference('sup-', [status(thm)], ['192', '193'])).
% 4.78/5.03  thf('195', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) | 
% 4.78/5.03       (![X19 : $i]: (zip_tseitin_0 @ X19 @ sk_C @ sk_B))),
% 4.78/5.03      inference('split', [status(esa)], ['60'])).
% 4.78/5.03  thf('196', plain,
% 4.78/5.03      ((~ (zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)
% 4.78/5.03        | ~ (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))
% 4.78/5.03        | ~ (zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)
% 4.78/5.03        | ((sk_B) != (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('197', plain,
% 4.78/5.03      (~ ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))) | 
% 4.78/5.03       ~ ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)) | 
% 4.78/5.03       ~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) | 
% 4.78/5.03       ~ (((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('split', [status(esa)], ['196'])).
% 4.78/5.03  thf('198', plain,
% 4.78/5.03      (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A))
% 4.78/5.03         <= (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('199', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.78/5.03         ((r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 4.78/5.03          | ~ (zip_tseitin_1 @ X13 @ X14 @ X15))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('200', plain,
% 4.78/5.03      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C)))
% 4.78/5.03         <= (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['198', '199'])).
% 4.78/5.03  thf('201', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X7)
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X6 @ (k1_funct_1 @ X7 @ X6)) @ X7)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['1'])).
% 4.78/5.03  thf('202', plain,
% 4.78/5.03      ((((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_C @ sk_D_2)) @ 
% 4.78/5.03          sk_C)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_C)
% 4.78/5.03         | ~ (v1_relat_1 @ sk_C)))
% 4.78/5.03         <= (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['200', '201'])).
% 4.78/5.03  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('205', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_C @ sk_D_2)) @ sk_C))
% 4.78/5.03         <= (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('demod', [status(thm)], ['202', '203', '204'])).
% 4.78/5.03  thf('206', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('207', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X0)
% 4.78/5.03          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 4.78/5.03          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 4.78/5.03          | ~ (r2_hidden @ X4 @ X1)
% 4.78/5.03          | ~ (v1_relat_1 @ X2))),
% 4.78/5.03      inference('cnf', [status(esa)], [d12_relat_1])).
% 4.78/5.03  thf('208', plain,
% 4.78/5.03      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X2)
% 4.78/5.03          | ~ (r2_hidden @ X4 @ X1)
% 4.78/5.03          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k8_relat_1 @ X1 @ X2))
% 4.78/5.03          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['207'])).
% 4.78/5.03  thf('209', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (v1_relat_1 @ sk_B)
% 4.78/5.03           | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k8_relat_1 @ sk_A @ sk_C))
% 4.78/5.03           | ~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)
% 4.78/5.03           | ~ (r2_hidden @ X0 @ sk_A)
% 4.78/5.03           | ~ (v1_relat_1 @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['206', '208'])).
% 4.78/5.03  thf('210', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('211', plain,
% 4.78/5.03      ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('split', [status(esa)], ['4'])).
% 4.78/5.03  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('213', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          ((r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | ~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)
% 4.78/5.03           | ~ (r2_hidden @ X0 @ sk_A)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 4.78/5.03  thf('214', plain,
% 4.78/5.03      (((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_D_2) @ sk_A)
% 4.78/5.03         | (r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_C @ sk_D_2)) @ 
% 4.78/5.03            sk_B)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['205', '213'])).
% 4.78/5.03  thf('215', plain,
% 4.78/5.03      (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A))
% 4.78/5.03         <= (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('216', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.78/5.03         ((r2_hidden @ (k1_funct_1 @ X14 @ X13) @ X15)
% 4.78/5.03          | ~ (zip_tseitin_1 @ X13 @ X14 @ X15))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('217', plain,
% 4.78/5.03      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_D_2) @ sk_A))
% 4.78/5.03         <= (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['215', '216'])).
% 4.78/5.03  thf('218', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_C @ sk_D_2)) @ sk_B))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('demod', [status(thm)], ['214', '217'])).
% 4.78/5.03  thf('219', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('220', plain,
% 4.78/5.03      (((~ (v1_relat_1 @ sk_B)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03         | (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['218', '219'])).
% 4.78/5.03  thf('221', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('222', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('223', plain,
% 4.78/5.03      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('demod', [status(thm)], ['220', '221', '222'])).
% 4.78/5.03  thf('224', plain,
% 4.78/5.03      ((~ (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('split', [status(esa)], ['196'])).
% 4.78/5.03  thf('225', plain,
% 4.78/5.03      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))) | 
% 4.78/5.03       ~ ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)) | 
% 4.78/5.03       ~ (((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['223', '224'])).
% 4.78/5.03  thf('226', plain,
% 4.78/5.03      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))) | 
% 4.78/5.03       ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)) | 
% 4.78/5.03       ~ ((zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B)) | 
% 4.78/5.03       ~ (((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('227', plain,
% 4.78/5.03      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B)))
% 4.78/5.03         <= (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('split', [status(esa)], ['21'])).
% 4.78/5.03  thf('228', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i]:
% 4.78/5.03         (~ (v1_relat_1 @ X7)
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | (r2_hidden @ (k4_tarski @ X6 @ (k1_funct_1 @ X7 @ X6)) @ X7)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['1'])).
% 4.78/5.03  thf('229', plain,
% 4.78/5.03      ((((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_B @ sk_D_2)) @ 
% 4.78/5.03          sk_B)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_B)
% 4.78/5.03         | ~ (v1_relat_1 @ sk_B)))
% 4.78/5.03         <= (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['227', '228'])).
% 4.78/5.03  thf('230', plain, ((v1_funct_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('231', plain, ((v1_relat_1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('232', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_B @ sk_D_2)) @ sk_B))
% 4.78/5.03         <= (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('demod', [status(thm)], ['229', '230', '231'])).
% 4.78/5.03  thf('233', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | (r2_hidden @ X0 @ sk_A)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 4.78/5.03  thf('234', plain,
% 4.78/5.03      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_D_2) @ sk_A))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['232', '233'])).
% 4.78/5.03  thf('235', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_B @ sk_D_2)) @ sk_B))
% 4.78/5.03         <= (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('demod', [status(thm)], ['229', '230', '231'])).
% 4.78/5.03  thf('236', plain,
% 4.78/5.03      ((![X0 : $i, X1 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 4.78/5.03           | (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))))),
% 4.78/5.03      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 4.78/5.03  thf('237', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_B @ sk_D_2)) @ sk_C))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['235', '236'])).
% 4.78/5.03  thf('238', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | ((X8) = (k1_funct_1 @ X7 @ X6))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('239', plain,
% 4.78/5.03      (((~ (v1_relat_1 @ sk_C)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_C)
% 4.78/5.03         | ((k1_funct_1 @ sk_B @ sk_D_2) = (k1_funct_1 @ sk_C @ sk_D_2))))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['237', '238'])).
% 4.78/5.03  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('242', plain,
% 4.78/5.03      ((((k1_funct_1 @ sk_B @ sk_D_2) = (k1_funct_1 @ sk_C @ sk_D_2)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('demod', [status(thm)], ['239', '240', '241'])).
% 4.78/5.03  thf('243', plain,
% 4.78/5.03      (![X13 : $i, X14 : $i, X16 : $i]:
% 4.78/5.03         ((zip_tseitin_1 @ X13 @ X14 @ X16)
% 4.78/5.03          | ~ (r2_hidden @ (k1_funct_1 @ X14 @ X13) @ X16)
% 4.78/5.03          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X14)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('244', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_D_2) @ X0)
% 4.78/5.03           | ~ (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C))
% 4.78/5.03           | (zip_tseitin_1 @ sk_D_2 @ sk_C @ X0)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['242', '243'])).
% 4.78/5.03  thf('245', plain,
% 4.78/5.03      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (k1_funct_1 @ sk_B @ sk_D_2)) @ sk_C))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['235', '236'])).
% 4.78/5.03  thf('246', plain,
% 4.78/5.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ X7)
% 4.78/5.03          | (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 4.78/5.03          | ~ (v1_funct_1 @ X7)
% 4.78/5.03          | ~ (v1_relat_1 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.78/5.03  thf('247', plain,
% 4.78/5.03      (((~ (v1_relat_1 @ sk_C)
% 4.78/5.03         | ~ (v1_funct_1 @ sk_C)
% 4.78/5.03         | (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C))))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['245', '246'])).
% 4.78/5.03  thf('248', plain, ((v1_relat_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('249', plain, ((v1_funct_1 @ sk_C)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.78/5.03  thf('250', plain,
% 4.78/5.03      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('demod', [status(thm)], ['247', '248', '249'])).
% 4.78/5.03  thf('251', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_D_2) @ X0)
% 4.78/5.03           | (zip_tseitin_1 @ sk_D_2 @ sk_C @ X0)))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('demod', [status(thm)], ['244', '250'])).
% 4.78/5.03  thf('252', plain,
% 4.78/5.03      (((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A))
% 4.78/5.03         <= ((((sk_B) = (k8_relat_1 @ sk_A @ sk_C))) & 
% 4.78/5.03             ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['234', '251'])).
% 4.78/5.03  thf('253', plain,
% 4.78/5.03      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A))
% 4.78/5.03         <= (~ ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)))),
% 4.78/5.03      inference('split', [status(esa)], ['196'])).
% 4.78/5.03  thf('254', plain,
% 4.78/5.03      (~ ((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_B))) | 
% 4.78/5.03       ((zip_tseitin_1 @ sk_D_2 @ sk_C @ sk_A)) | 
% 4.78/5.03       ~ (((sk_B) = (k8_relat_1 @ sk_A @ sk_C)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['252', '253'])).
% 4.78/5.03  thf('255', plain, ($false),
% 4.78/5.03      inference('sat_resolution*', [status(thm)],
% 4.78/5.03                ['49', '50', '52', '191', '194', '195', '197', '225', '226', 
% 4.78/5.03                 '254'])).
% 4.78/5.03  
% 4.78/5.03  % SZS output end Refutation
% 4.78/5.03  
% 4.78/5.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
