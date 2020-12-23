%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MdoQCKELfa

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:41 EST 2020

% Result     : Theorem 3.55s
% Output     : Refutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 858 expanded)
%              Number of leaves         :   21 ( 236 expanded)
%              Depth                    :   28
%              Number of atoms          : 1162 (16079 expanded)
%              Number of equality atoms :   74 (1804 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_5_type,type,(
    sk_D_5: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t156_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( A
                    = ( k2_relat_1 @ B ) )
                  & ( ( k1_relat_1 @ C )
                    = A )
                  & ( ( k1_relat_1 @ D )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k5_relat_1 @ B @ D ) ) )
               => ( C = D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ! [D: $i] :
                ( ( ( v1_relat_1 @ D )
                  & ( v1_funct_1 @ D ) )
               => ( ( ( A
                      = ( k2_relat_1 @ B ) )
                    & ( ( k1_relat_1 @ C )
                      = A )
                    & ( ( k1_relat_1 @ D )
                      = A )
                    & ( ( k5_relat_1 @ B @ C )
                      = ( k5_relat_1 @ B @ D ) ) )
                 => ( C = D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_D_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
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

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( sk_C_3 = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_C_3 = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_D_5 )
    | ( sk_C_3 = sk_D_5 )
    | ( r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A )
    | ( sk_C_3 = sk_D_5 )
    | ( r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_C_3 = sk_D_5 )
    | ( r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    sk_C_3 != sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( X24
       != ( k1_funct_1 @ X23 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_3 @ X0 ) ) @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_3 @ X0 ) ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) ) @ sk_C_3 ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('30',plain,(
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
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
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
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('33',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X16 @ X14 ) @ X16 ) @ X14 )
      | ( X15
       != ( k2_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('35',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X16 @ X14 ) @ X16 ) @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X0 @ sk_B ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('39',plain,(
    r2_hidden @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k1_funct_1 @ X19 @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['32','36'])).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_C @ sk_D_5 @ sk_C_3 )
      = ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_C @ sk_D_5 @ sk_C_3 )
    = ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','50'])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_3 )
    = ( k5_relat_1 @ sk_B @ sk_D_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','50'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_3 ) @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) )
      = ( k1_funct_1 @ sk_D_5 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) )
    | ~ ( v1_relat_1 @ sk_D_5 )
    | ~ ( v1_funct_1 @ sk_D_5 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_3 ) @ ( sk_D_4 @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_B ) )
    = ( k1_funct_1 @ sk_D_5 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
      = ( k1_funct_1 @ sk_D_5 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
    = ( k1_funct_1 @ sk_D_5 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
      = ( sk_D @ sk_D_5 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ( sk_C_3 = sk_D_5 )
    | ~ ( v1_relat_1 @ sk_D_5 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( ( sk_D @ sk_D_5 @ sk_C_3 )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_5 ) ),
    inference('sup+',[status(thm)],['31','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
      = ( sk_D @ sk_D_5 @ sk_C_3 ) )
    | ( sk_C_3 = sk_D_5 )
    | ( ( sk_D @ sk_D_5 @ sk_C_3 )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,
    ( ( sk_C_3 = sk_D_5 )
    | ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
      = ( sk_D @ sk_D_5 @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_C_3 != sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
    = ( sk_D @ sk_D_5 @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( sk_D @ sk_D_5 @ sk_C_3 ) ) @ sk_C_3 ),
    inference(demod,[status(thm)],['24','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ( sk_C_3 = sk_D_5 )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( sk_D @ sk_D_5 @ sk_C_3 ) ) @ sk_D_5 )
    | ~ ( v1_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_C_3 = sk_D_5 )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( sk_D @ sk_D_5 @ sk_C_3 ) ) @ sk_D_5 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    sk_C_3 != sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( sk_D @ sk_D_5 @ sk_C_3 ) ) @ sk_D_5 ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    r2_hidden @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_D_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_5 @ X0 ) ) @ sk_D_5 )
      | ~ ( v1_funct_1 @ sk_D_5 )
      | ~ ( v1_relat_1 @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_5 @ X0 ) ) @ sk_D_5 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( k1_funct_1 @ sk_D_5 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) ) @ sk_D_5 ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
    = ( k1_funct_1 @ sk_D_5 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('88',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) ) ) @ sk_D_5 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C @ sk_D_5 @ sk_C_3 ) )
    = ( sk_D @ sk_D_5 @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('90',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D_5 @ sk_C_3 ) @ ( sk_D @ sk_D_5 @ sk_C_3 ) ) @ sk_D_5 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['78','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MdoQCKELfa
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:42:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 3.55/3.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.55/3.77  % Solved by: fo/fo7.sh
% 3.55/3.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.55/3.77  % done 4298 iterations in 3.310s
% 3.55/3.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.55/3.77  % SZS output start Refutation
% 3.55/3.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.55/3.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.55/3.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.55/3.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.55/3.77  thf(sk_C_3_type, type, sk_C_3: $i).
% 3.55/3.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.55/3.77  thf(sk_D_5_type, type, sk_D_5: $i).
% 3.55/3.77  thf(sk_A_type, type, sk_A: $i).
% 3.55/3.77  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.55/3.77  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 3.55/3.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.55/3.77  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.55/3.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.55/3.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.55/3.77  thf(sk_B_type, type, sk_B: $i).
% 3.55/3.77  thf(t156_funct_1, conjecture,
% 3.55/3.77    (![A:$i,B:$i]:
% 3.55/3.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.55/3.77       ( ![C:$i]:
% 3.55/3.77         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.55/3.77           ( ![D:$i]:
% 3.55/3.77             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 3.55/3.77               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 3.55/3.77                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 3.55/3.77                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 3.55/3.77                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 3.55/3.77                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 3.55/3.77  thf(zf_stmt_0, negated_conjecture,
% 3.55/3.77    (~( ![A:$i,B:$i]:
% 3.55/3.77        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.55/3.77          ( ![C:$i]:
% 3.55/3.77            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.55/3.77              ( ![D:$i]:
% 3.55/3.77                ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 3.55/3.77                  ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 3.55/3.77                      ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 3.55/3.77                      ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 3.55/3.77                      ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 3.55/3.77                    ( ( C ) = ( D ) ) ) ) ) ) ) ) )),
% 3.55/3.77    inference('cnf.neg', [status(esa)], [t156_funct_1])).
% 3.55/3.77  thf('0', plain, (((k1_relat_1 @ sk_D_5) = (sk_A))),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf('1', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf(d2_relat_1, axiom,
% 3.55/3.77    (![A:$i]:
% 3.55/3.77     ( ( v1_relat_1 @ A ) =>
% 3.55/3.77       ( ![B:$i]:
% 3.55/3.77         ( ( v1_relat_1 @ B ) =>
% 3.55/3.77           ( ( ( A ) = ( B ) ) <=>
% 3.55/3.77             ( ![C:$i,D:$i]:
% 3.55/3.77               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 3.55/3.77                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 3.55/3.77  thf('2', plain,
% 3.55/3.77      (![X0 : $i, X1 : $i]:
% 3.55/3.77         (~ (v1_relat_1 @ X0)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 3.55/3.77          | ((X1) = (X0))
% 3.55/3.77          | ~ (v1_relat_1 @ X1))),
% 3.55/3.77      inference('cnf', [status(esa)], [d2_relat_1])).
% 3.55/3.77  thf(d4_relat_1, axiom,
% 3.55/3.77    (![A:$i,B:$i]:
% 3.55/3.77     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.55/3.77       ( ![C:$i]:
% 3.55/3.77         ( ( r2_hidden @ C @ B ) <=>
% 3.55/3.77           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.55/3.77  thf('3', plain,
% 3.55/3.77      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.55/3.77         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 3.55/3.77          | (r2_hidden @ X5 @ X8)
% 3.55/3.77          | ((X8) != (k1_relat_1 @ X7)))),
% 3.55/3.77      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.55/3.77  thf('4', plain,
% 3.55/3.77      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.55/3.77         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 3.55/3.77          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 3.55/3.77      inference('simplify', [status(thm)], ['3'])).
% 3.55/3.77  thf('5', plain,
% 3.55/3.77      (![X0 : $i, X1 : $i]:
% 3.55/3.77         (~ (v1_relat_1 @ X0)
% 3.55/3.77          | ((X0) = (X1))
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 3.55/3.77          | ~ (v1_relat_1 @ X1)
% 3.55/3.77          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.55/3.77      inference('sup-', [status(thm)], ['2', '4'])).
% 3.55/3.77  thf('6', plain,
% 3.55/3.77      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.55/3.77         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 3.55/3.77          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 3.55/3.77      inference('simplify', [status(thm)], ['3'])).
% 3.55/3.77  thf('7', plain,
% 3.55/3.77      (![X0 : $i, X1 : $i]:
% 3.55/3.77         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 3.55/3.77          | ~ (v1_relat_1 @ X0)
% 3.55/3.77          | ((X1) = (X0))
% 3.55/3.77          | ~ (v1_relat_1 @ X1)
% 3.55/3.77          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 3.55/3.77      inference('sup-', [status(thm)], ['5', '6'])).
% 3.55/3.77  thf('8', plain,
% 3.55/3.77      (![X0 : $i]:
% 3.55/3.77         ((r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_A)
% 3.55/3.77          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ (k1_relat_1 @ X0))
% 3.55/3.77          | ~ (v1_relat_1 @ sk_C_3)
% 3.55/3.77          | ((sk_C_3) = (X0))
% 3.55/3.77          | ~ (v1_relat_1 @ X0))),
% 3.55/3.77      inference('sup+', [status(thm)], ['1', '7'])).
% 3.55/3.77  thf('9', plain, ((v1_relat_1 @ sk_C_3)),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf('10', plain,
% 3.55/3.77      (![X0 : $i]:
% 3.55/3.77         ((r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_A)
% 3.55/3.77          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ (k1_relat_1 @ X0))
% 3.55/3.77          | ((sk_C_3) = (X0))
% 3.55/3.77          | ~ (v1_relat_1 @ X0))),
% 3.55/3.77      inference('demod', [status(thm)], ['8', '9'])).
% 3.55/3.77  thf('11', plain,
% 3.55/3.77      (((r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A)
% 3.55/3.77        | ~ (v1_relat_1 @ sk_D_5)
% 3.55/3.77        | ((sk_C_3) = (sk_D_5))
% 3.55/3.77        | (r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A))),
% 3.55/3.77      inference('sup+', [status(thm)], ['0', '10'])).
% 3.55/3.77  thf('12', plain, ((v1_relat_1 @ sk_D_5)),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf('13', plain,
% 3.55/3.77      (((r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A)
% 3.55/3.77        | ((sk_C_3) = (sk_D_5))
% 3.55/3.77        | (r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A))),
% 3.55/3.77      inference('demod', [status(thm)], ['11', '12'])).
% 3.55/3.77  thf('14', plain,
% 3.55/3.77      ((((sk_C_3) = (sk_D_5)) | (r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A))),
% 3.55/3.77      inference('simplify', [status(thm)], ['13'])).
% 3.55/3.77  thf('15', plain, (((sk_C_3) != (sk_D_5))),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf('16', plain, ((r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A)),
% 3.55/3.77      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 3.55/3.77  thf('17', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf(t8_funct_1, axiom,
% 3.55/3.77    (![A:$i,B:$i,C:$i]:
% 3.55/3.77     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.55/3.77       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 3.55/3.77         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 3.55/3.77           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 3.55/3.77  thf('18', plain,
% 3.55/3.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.55/3.77         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 3.55/3.77          | ((X24) != (k1_funct_1 @ X23 @ X22))
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 3.55/3.77          | ~ (v1_funct_1 @ X23)
% 3.55/3.77          | ~ (v1_relat_1 @ X23))),
% 3.55/3.77      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.55/3.77  thf('19', plain,
% 3.55/3.77      (![X22 : $i, X23 : $i]:
% 3.55/3.77         (~ (v1_relat_1 @ X23)
% 3.55/3.77          | ~ (v1_funct_1 @ X23)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 3.55/3.77          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 3.55/3.77      inference('simplify', [status(thm)], ['18'])).
% 3.55/3.77  thf('20', plain,
% 3.55/3.77      (![X0 : $i]:
% 3.55/3.77         (~ (r2_hidden @ X0 @ sk_A)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_3 @ X0)) @ sk_C_3)
% 3.55/3.77          | ~ (v1_funct_1 @ sk_C_3)
% 3.55/3.77          | ~ (v1_relat_1 @ sk_C_3))),
% 3.55/3.77      inference('sup-', [status(thm)], ['17', '19'])).
% 3.55/3.77  thf('21', plain, ((v1_funct_1 @ sk_C_3)),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf('22', plain, ((v1_relat_1 @ sk_C_3)),
% 3.55/3.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.77  thf('23', plain,
% 3.55/3.77      (![X0 : $i]:
% 3.55/3.77         (~ (r2_hidden @ X0 @ sk_A)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_3 @ X0)) @ sk_C_3))),
% 3.55/3.77      inference('demod', [status(thm)], ['20', '21', '22'])).
% 3.55/3.77  thf('24', plain,
% 3.55/3.77      ((r2_hidden @ 
% 3.55/3.77        (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ 
% 3.55/3.77         (k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))) @ 
% 3.55/3.77        sk_C_3)),
% 3.55/3.77      inference('sup-', [status(thm)], ['16', '23'])).
% 3.55/3.77  thf('25', plain,
% 3.55/3.77      (![X0 : $i, X1 : $i]:
% 3.55/3.77         (~ (v1_relat_1 @ X0)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 3.55/3.77          | ((X1) = (X0))
% 3.55/3.77          | ~ (v1_relat_1 @ X1))),
% 3.55/3.77      inference('cnf', [status(esa)], [d2_relat_1])).
% 3.55/3.77  thf('26', plain,
% 3.55/3.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.55/3.77         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 3.55/3.77          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 3.55/3.77          | ~ (v1_funct_1 @ X23)
% 3.55/3.77          | ~ (v1_relat_1 @ X23))),
% 3.55/3.77      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.55/3.77  thf('27', plain,
% 3.55/3.77      (![X0 : $i, X1 : $i]:
% 3.55/3.77         (~ (v1_relat_1 @ X0)
% 3.55/3.77          | ((X0) = (X1))
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 3.55/3.77          | ~ (v1_relat_1 @ X1)
% 3.55/3.77          | ~ (v1_relat_1 @ X0)
% 3.55/3.77          | ~ (v1_funct_1 @ X0)
% 3.55/3.77          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0))))),
% 3.55/3.77      inference('sup-', [status(thm)], ['25', '26'])).
% 3.55/3.77  thf('28', plain,
% 3.55/3.77      (![X0 : $i, X1 : $i]:
% 3.55/3.77         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 3.55/3.77          | ~ (v1_funct_1 @ X0)
% 3.55/3.77          | ~ (v1_relat_1 @ X1)
% 3.55/3.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 3.55/3.77          | ((X0) = (X1))
% 3.55/3.77          | ~ (v1_relat_1 @ X0))),
% 3.55/3.77      inference('simplify', [status(thm)], ['27'])).
% 3.55/3.77  thf('29', plain,
% 3.55/3.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.55/3.78         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 3.55/3.78          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 3.55/3.78          | ~ (v1_funct_1 @ X23)
% 3.55/3.78          | ~ (v1_relat_1 @ X23))),
% 3.55/3.78      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.55/3.78  thf('30', plain,
% 3.55/3.78      (![X0 : $i, X1 : $i]:
% 3.55/3.78         (~ (v1_relat_1 @ X1)
% 3.55/3.78          | ((X1) = (X0))
% 3.55/3.78          | ~ (v1_relat_1 @ X0)
% 3.55/3.78          | ~ (v1_funct_1 @ X1)
% 3.55/3.78          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 3.55/3.78          | ~ (v1_relat_1 @ X0)
% 3.55/3.78          | ~ (v1_funct_1 @ X0)
% 3.55/3.78          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1))))),
% 3.55/3.78      inference('sup-', [status(thm)], ['28', '29'])).
% 3.55/3.78  thf('31', plain,
% 3.55/3.78      (![X0 : $i, X1 : $i]:
% 3.55/3.78         (((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1)))
% 3.55/3.78          | ~ (v1_funct_1 @ X0)
% 3.55/3.78          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 3.55/3.78          | ~ (v1_funct_1 @ X1)
% 3.55/3.78          | ~ (v1_relat_1 @ X0)
% 3.55/3.78          | ((X1) = (X0))
% 3.55/3.78          | ~ (v1_relat_1 @ X1))),
% 3.55/3.78      inference('simplify', [status(thm)], ['30'])).
% 3.55/3.78  thf('32', plain, ((r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A)),
% 3.55/3.78      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 3.55/3.78  thf('33', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf(d5_relat_1, axiom,
% 3.55/3.78    (![A:$i,B:$i]:
% 3.55/3.78     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.55/3.78       ( ![C:$i]:
% 3.55/3.78         ( ( r2_hidden @ C @ B ) <=>
% 3.55/3.78           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.55/3.78  thf('34', plain,
% 3.55/3.78      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.55/3.78         (~ (r2_hidden @ X16 @ X15)
% 3.55/3.78          | (r2_hidden @ (k4_tarski @ (sk_D_4 @ X16 @ X14) @ X16) @ X14)
% 3.55/3.78          | ((X15) != (k2_relat_1 @ X14)))),
% 3.55/3.78      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.55/3.78  thf('35', plain,
% 3.55/3.78      (![X14 : $i, X16 : $i]:
% 3.55/3.78         ((r2_hidden @ (k4_tarski @ (sk_D_4 @ X16 @ X14) @ X16) @ X14)
% 3.55/3.78          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X14)))),
% 3.55/3.78      inference('simplify', [status(thm)], ['34'])).
% 3.55/3.78  thf('36', plain,
% 3.55/3.78      (![X0 : $i]:
% 3.55/3.78         (~ (r2_hidden @ X0 @ sk_A)
% 3.55/3.78          | (r2_hidden @ (k4_tarski @ (sk_D_4 @ X0 @ sk_B) @ X0) @ sk_B))),
% 3.55/3.78      inference('sup-', [status(thm)], ['33', '35'])).
% 3.55/3.78  thf('37', plain,
% 3.55/3.78      ((r2_hidden @ 
% 3.55/3.78        (k4_tarski @ (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B) @ 
% 3.55/3.78         (sk_C @ sk_D_5 @ sk_C_3)) @ 
% 3.55/3.78        sk_B)),
% 3.55/3.78      inference('sup-', [status(thm)], ['32', '36'])).
% 3.55/3.78  thf('38', plain,
% 3.55/3.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.55/3.78         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 3.55/3.78          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 3.55/3.78      inference('simplify', [status(thm)], ['3'])).
% 3.55/3.78  thf('39', plain,
% 3.55/3.78      ((r2_hidden @ (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B) @ 
% 3.55/3.78        (k1_relat_1 @ sk_B))),
% 3.55/3.78      inference('sup-', [status(thm)], ['37', '38'])).
% 3.55/3.78  thf(t23_funct_1, axiom,
% 3.55/3.78    (![A:$i,B:$i]:
% 3.55/3.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.55/3.78       ( ![C:$i]:
% 3.55/3.78         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.55/3.78           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 3.55/3.78             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.55/3.78               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 3.55/3.78  thf('40', plain,
% 3.55/3.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.55/3.78         (~ (v1_relat_1 @ X19)
% 3.55/3.78          | ~ (v1_funct_1 @ X19)
% 3.55/3.78          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 3.55/3.78              = (k1_funct_1 @ X19 @ (k1_funct_1 @ X20 @ X21)))
% 3.55/3.78          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 3.55/3.78          | ~ (v1_funct_1 @ X20)
% 3.55/3.78          | ~ (v1_relat_1 @ X20))),
% 3.55/3.78      inference('cnf', [status(esa)], [t23_funct_1])).
% 3.55/3.78  thf('41', plain,
% 3.55/3.78      (![X0 : $i]:
% 3.55/3.78         (~ (v1_relat_1 @ sk_B)
% 3.55/3.78          | ~ (v1_funct_1 @ sk_B)
% 3.55/3.78          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 3.55/3.78              (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))
% 3.55/3.78              = (k1_funct_1 @ X0 @ 
% 3.55/3.78                 (k1_funct_1 @ sk_B @ 
% 3.55/3.78                  (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))))
% 3.55/3.78          | ~ (v1_funct_1 @ X0)
% 3.55/3.78          | ~ (v1_relat_1 @ X0))),
% 3.55/3.78      inference('sup-', [status(thm)], ['39', '40'])).
% 3.55/3.78  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('44', plain,
% 3.55/3.78      (![X0 : $i]:
% 3.55/3.78         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 3.55/3.78            (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))
% 3.55/3.78            = (k1_funct_1 @ X0 @ 
% 3.55/3.78               (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))))
% 3.55/3.78          | ~ (v1_funct_1 @ X0)
% 3.55/3.78          | ~ (v1_relat_1 @ X0))),
% 3.55/3.78      inference('demod', [status(thm)], ['41', '42', '43'])).
% 3.55/3.78  thf('45', plain,
% 3.55/3.78      ((r2_hidden @ 
% 3.55/3.78        (k4_tarski @ (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B) @ 
% 3.55/3.78         (sk_C @ sk_D_5 @ sk_C_3)) @ 
% 3.55/3.78        sk_B)),
% 3.55/3.78      inference('sup-', [status(thm)], ['32', '36'])).
% 3.55/3.78  thf('46', plain,
% 3.55/3.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.55/3.78         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 3.55/3.78          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 3.55/3.78          | ~ (v1_funct_1 @ X23)
% 3.55/3.78          | ~ (v1_relat_1 @ X23))),
% 3.55/3.78      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.55/3.78  thf('47', plain,
% 3.55/3.78      ((~ (v1_relat_1 @ sk_B)
% 3.55/3.78        | ~ (v1_funct_1 @ sk_B)
% 3.55/3.78        | ((sk_C @ sk_D_5 @ sk_C_3)
% 3.55/3.78            = (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))))),
% 3.55/3.78      inference('sup-', [status(thm)], ['45', '46'])).
% 3.55/3.78  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('50', plain,
% 3.55/3.78      (((sk_C @ sk_D_5 @ sk_C_3)
% 3.55/3.78         = (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B)))),
% 3.55/3.78      inference('demod', [status(thm)], ['47', '48', '49'])).
% 3.55/3.78  thf('51', plain,
% 3.55/3.78      (![X0 : $i]:
% 3.55/3.78         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 3.55/3.78            (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))
% 3.55/3.78            = (k1_funct_1 @ X0 @ (sk_C @ sk_D_5 @ sk_C_3)))
% 3.55/3.78          | ~ (v1_funct_1 @ X0)
% 3.55/3.78          | ~ (v1_relat_1 @ X0))),
% 3.55/3.78      inference('demod', [status(thm)], ['44', '50'])).
% 3.55/3.78  thf('52', plain,
% 3.55/3.78      (((k5_relat_1 @ sk_B @ sk_C_3) = (k5_relat_1 @ sk_B @ sk_D_5))),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('53', plain,
% 3.55/3.78      (![X0 : $i]:
% 3.55/3.78         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 3.55/3.78            (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))
% 3.55/3.78            = (k1_funct_1 @ X0 @ (sk_C @ sk_D_5 @ sk_C_3)))
% 3.55/3.78          | ~ (v1_funct_1 @ X0)
% 3.55/3.78          | ~ (v1_relat_1 @ X0))),
% 3.55/3.78      inference('demod', [status(thm)], ['44', '50'])).
% 3.55/3.78  thf('54', plain,
% 3.55/3.78      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_3) @ 
% 3.55/3.78          (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))
% 3.55/3.78          = (k1_funct_1 @ sk_D_5 @ (sk_C @ sk_D_5 @ sk_C_3)))
% 3.55/3.78        | ~ (v1_relat_1 @ sk_D_5)
% 3.55/3.78        | ~ (v1_funct_1 @ sk_D_5))),
% 3.55/3.78      inference('sup+', [status(thm)], ['52', '53'])).
% 3.55/3.78  thf('55', plain, ((v1_relat_1 @ sk_D_5)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('56', plain, ((v1_funct_1 @ sk_D_5)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('57', plain,
% 3.55/3.78      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_3) @ 
% 3.55/3.78         (sk_D_4 @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_B))
% 3.55/3.78         = (k1_funct_1 @ sk_D_5 @ (sk_C @ sk_D_5 @ sk_C_3)))),
% 3.55/3.78      inference('demod', [status(thm)], ['54', '55', '56'])).
% 3.55/3.78  thf('58', plain,
% 3.55/3.78      ((((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78          = (k1_funct_1 @ sk_D_5 @ (sk_C @ sk_D_5 @ sk_C_3)))
% 3.55/3.78        | ~ (v1_relat_1 @ sk_C_3)
% 3.55/3.78        | ~ (v1_funct_1 @ sk_C_3))),
% 3.55/3.78      inference('sup+', [status(thm)], ['51', '57'])).
% 3.55/3.78  thf('59', plain, ((v1_relat_1 @ sk_C_3)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('60', plain, ((v1_funct_1 @ sk_C_3)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('61', plain,
% 3.55/3.78      (((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78         = (k1_funct_1 @ sk_D_5 @ (sk_C @ sk_D_5 @ sk_C_3)))),
% 3.55/3.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 3.55/3.78  thf('62', plain,
% 3.55/3.78      ((((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78          = (sk_D @ sk_D_5 @ sk_C_3))
% 3.55/3.78        | ~ (v1_relat_1 @ sk_C_3)
% 3.55/3.78        | ((sk_C_3) = (sk_D_5))
% 3.55/3.78        | ~ (v1_relat_1 @ sk_D_5)
% 3.55/3.78        | ~ (v1_funct_1 @ sk_C_3)
% 3.55/3.78        | ((sk_D @ sk_D_5 @ sk_C_3)
% 3.55/3.78            = (k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3)))
% 3.55/3.78        | ~ (v1_funct_1 @ sk_D_5))),
% 3.55/3.78      inference('sup+', [status(thm)], ['31', '61'])).
% 3.55/3.78  thf('63', plain, ((v1_relat_1 @ sk_C_3)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('64', plain, ((v1_relat_1 @ sk_D_5)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('65', plain, ((v1_funct_1 @ sk_C_3)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('66', plain, ((v1_funct_1 @ sk_D_5)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('67', plain,
% 3.55/3.78      ((((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78          = (sk_D @ sk_D_5 @ sk_C_3))
% 3.55/3.78        | ((sk_C_3) = (sk_D_5))
% 3.55/3.78        | ((sk_D @ sk_D_5 @ sk_C_3)
% 3.55/3.78            = (k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))))),
% 3.55/3.78      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 3.55/3.78  thf('68', plain,
% 3.55/3.78      ((((sk_C_3) = (sk_D_5))
% 3.55/3.78        | ((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78            = (sk_D @ sk_D_5 @ sk_C_3)))),
% 3.55/3.78      inference('simplify', [status(thm)], ['67'])).
% 3.55/3.78  thf('69', plain, (((sk_C_3) != (sk_D_5))),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('70', plain,
% 3.55/3.78      (((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78         = (sk_D @ sk_D_5 @ sk_C_3))),
% 3.55/3.78      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 3.55/3.78  thf('71', plain,
% 3.55/3.78      ((r2_hidden @ 
% 3.55/3.78        (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ (sk_D @ sk_D_5 @ sk_C_3)) @ 
% 3.55/3.78        sk_C_3)),
% 3.55/3.78      inference('demod', [status(thm)], ['24', '70'])).
% 3.55/3.78  thf('72', plain,
% 3.55/3.78      (![X0 : $i, X1 : $i]:
% 3.55/3.78         (~ (v1_relat_1 @ X0)
% 3.55/3.78          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 3.55/3.78               X1)
% 3.55/3.78          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 3.55/3.78               X0)
% 3.55/3.78          | ((X1) = (X0))
% 3.55/3.78          | ~ (v1_relat_1 @ X1))),
% 3.55/3.78      inference('cnf', [status(esa)], [d2_relat_1])).
% 3.55/3.78  thf('73', plain,
% 3.55/3.78      ((~ (v1_relat_1 @ sk_C_3)
% 3.55/3.78        | ((sk_C_3) = (sk_D_5))
% 3.55/3.78        | ~ (r2_hidden @ 
% 3.55/3.78             (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ (sk_D @ sk_D_5 @ sk_C_3)) @ 
% 3.55/3.78             sk_D_5)
% 3.55/3.78        | ~ (v1_relat_1 @ sk_D_5))),
% 3.55/3.78      inference('sup-', [status(thm)], ['71', '72'])).
% 3.55/3.78  thf('74', plain, ((v1_relat_1 @ sk_C_3)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('75', plain, ((v1_relat_1 @ sk_D_5)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('76', plain,
% 3.55/3.78      ((((sk_C_3) = (sk_D_5))
% 3.55/3.78        | ~ (r2_hidden @ 
% 3.55/3.78             (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ (sk_D @ sk_D_5 @ sk_C_3)) @ 
% 3.55/3.78             sk_D_5))),
% 3.55/3.78      inference('demod', [status(thm)], ['73', '74', '75'])).
% 3.55/3.78  thf('77', plain, (((sk_C_3) != (sk_D_5))),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('78', plain,
% 3.55/3.78      (~ (r2_hidden @ 
% 3.55/3.78          (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ (sk_D @ sk_D_5 @ sk_C_3)) @ 
% 3.55/3.78          sk_D_5)),
% 3.55/3.78      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 3.55/3.78  thf('79', plain, ((r2_hidden @ (sk_C @ sk_D_5 @ sk_C_3) @ sk_A)),
% 3.55/3.78      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 3.55/3.78  thf('80', plain, (((k1_relat_1 @ sk_D_5) = (sk_A))),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('81', plain,
% 3.55/3.78      (![X22 : $i, X23 : $i]:
% 3.55/3.78         (~ (v1_relat_1 @ X23)
% 3.55/3.78          | ~ (v1_funct_1 @ X23)
% 3.55/3.78          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 3.55/3.78          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 3.55/3.78      inference('simplify', [status(thm)], ['18'])).
% 3.55/3.78  thf('82', plain,
% 3.55/3.78      (![X0 : $i]:
% 3.55/3.78         (~ (r2_hidden @ X0 @ sk_A)
% 3.55/3.78          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_5 @ X0)) @ sk_D_5)
% 3.55/3.78          | ~ (v1_funct_1 @ sk_D_5)
% 3.55/3.78          | ~ (v1_relat_1 @ sk_D_5))),
% 3.55/3.78      inference('sup-', [status(thm)], ['80', '81'])).
% 3.55/3.78  thf('83', plain, ((v1_funct_1 @ sk_D_5)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('84', plain, ((v1_relat_1 @ sk_D_5)),
% 3.55/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.78  thf('85', plain,
% 3.55/3.78      (![X0 : $i]:
% 3.55/3.78         (~ (r2_hidden @ X0 @ sk_A)
% 3.55/3.78          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_5 @ X0)) @ sk_D_5))),
% 3.55/3.78      inference('demod', [status(thm)], ['82', '83', '84'])).
% 3.55/3.78  thf('86', plain,
% 3.55/3.78      ((r2_hidden @ 
% 3.55/3.78        (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ 
% 3.55/3.78         (k1_funct_1 @ sk_D_5 @ (sk_C @ sk_D_5 @ sk_C_3))) @ 
% 3.55/3.78        sk_D_5)),
% 3.55/3.78      inference('sup-', [status(thm)], ['79', '85'])).
% 3.55/3.78  thf('87', plain,
% 3.55/3.78      (((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78         = (k1_funct_1 @ sk_D_5 @ (sk_C @ sk_D_5 @ sk_C_3)))),
% 3.55/3.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 3.55/3.78  thf('88', plain,
% 3.55/3.78      ((r2_hidden @ 
% 3.55/3.78        (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ 
% 3.55/3.78         (k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))) @ 
% 3.55/3.78        sk_D_5)),
% 3.55/3.78      inference('demod', [status(thm)], ['86', '87'])).
% 3.55/3.78  thf('89', plain,
% 3.55/3.78      (((k1_funct_1 @ sk_C_3 @ (sk_C @ sk_D_5 @ sk_C_3))
% 3.55/3.78         = (sk_D @ sk_D_5 @ sk_C_3))),
% 3.55/3.78      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 3.55/3.78  thf('90', plain,
% 3.55/3.78      ((r2_hidden @ 
% 3.55/3.78        (k4_tarski @ (sk_C @ sk_D_5 @ sk_C_3) @ (sk_D @ sk_D_5 @ sk_C_3)) @ 
% 3.55/3.78        sk_D_5)),
% 3.55/3.78      inference('demod', [status(thm)], ['88', '89'])).
% 3.55/3.78  thf('91', plain, ($false), inference('demod', [status(thm)], ['78', '90'])).
% 3.55/3.78  
% 3.55/3.78  % SZS output end Refutation
% 3.55/3.78  
% 3.55/3.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
