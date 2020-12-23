%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LifgUR3zkD

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:41 EST 2020

% Result     : Theorem 4.55s
% Output     : Refutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 749 expanded)
%              Number of leaves         :   23 ( 213 expanded)
%              Depth                    :   36
%              Number of atoms          : 1567 (14187 expanded)
%              Number of equality atoms :   57 (1465 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X4 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
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

thf('9',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('10',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

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

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k1_funct_1 @ X18 @ ( k1_funct_1 @ X19 @ X20 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X1 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X1 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X4 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('26',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_2 @ X15 @ X12 ) ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('28',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_2 @ X15 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( sk_C @ X0 @ sk_C_2 )
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('35',plain,(
    ! [X12: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( X16
       != ( k1_funct_1 @ X12 @ X17 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('36',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( X23
       != ( k1_funct_1 @ X22 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( k1_funct_1 @ X22 @ X21 ) ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_C_2 ) ) ) @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_C_2 ) ) ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( sk_D @ X0 @ sk_C_2 ) ) @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( sk_D @ X0 @ sk_C_2 ) ) @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( sk_D @ X0 @ sk_C_2 ) ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_C_2 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_C_2 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X1 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( sk_C @ X0 @ sk_C_2 )
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_D_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( k1_funct_1 @ X22 @ X21 ) ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_3 @ X0 ) ) @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_3 @ X0 ) ) @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) @ ( k1_funct_1 @ sk_D_3 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_funct_1 @ sk_D_3 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) @ sk_D_3 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_funct_1 @ sk_D_3 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) ) @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_D_3 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','78'])).

thf('80',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_2 )
    = ( k5_relat_1 @ sk_B @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) @ sk_D_3 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_2 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ) @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_2 ) @ ( sk_D @ X0 @ sk_C_2 ) ) @ sk_D_3 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_C_2 ) @ ( sk_D @ X0 @ sk_C_2 ) ) @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X3 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('88',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_D_3 )
    | ( r1_tarski @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_C_2 @ sk_D_3 ),
    inference(simplify,[status(thm)],['90'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('92',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,
    ( ~ ( r1_tarski @ sk_D_3 @ sk_C_2 )
    | ( sk_D_3 = sk_C_2 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_C_2 != sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ~ ( r1_tarski @ sk_D_3 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('97',plain,(
    r1_tarski @ sk_C_2 @ sk_D_3 ),
    inference(simplify,[status(thm)],['90'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_D_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r1_tarski @ sk_D_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ sk_A )
      | ( r1_tarski @ sk_D_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_D_3 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_D_3 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) ) ) @ X1 )
      | ~ ( r1_tarski @ sk_C_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_D_3 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) ) ) @ X1 )
      | ~ ( r1_tarski @ sk_C_2 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_D_3 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) ) ) @ sk_D_3 )
      | ( r1_tarski @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ( X23
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) )
        = ( k1_funct_1 @ sk_D_3 @ ( sk_C @ X0 @ sk_D_3 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) )
        = ( k1_funct_1 @ sk_D_3 @ ( sk_C @ X0 @ sk_D_3 ) ) ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) )
        = ( sk_D @ X0 @ sk_D_3 ) )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r1_tarski @ sk_D_3 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( r1_tarski @ sk_D_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) )
        = ( sk_D @ X0 @ sk_D_3 ) )
      | ( r1_tarski @ sk_D_3 @ X0 )
      | ( r1_tarski @ sk_D_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) )
        = ( sk_D @ X0 @ sk_D_3 ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_D_3 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_D_3 ) ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_D_3 ) @ ( sk_D @ X0 @ sk_D_3 ) ) @ sk_C_2 )
      | ( r1_tarski @ sk_D_3 @ X0 )
      | ( r1_tarski @ sk_D_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_D_3 ) @ ( sk_D @ X0 @ sk_D_3 ) ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_D @ X3 @ X4 ) ) @ X3 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('124',plain,
    ( ( r1_tarski @ sk_D_3 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_D_3 )
    | ( r1_tarski @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r1_tarski @ sk_D_3 @ sk_C_2 )
    | ( r1_tarski @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tarski @ sk_D_3 @ sk_C_2 ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['95','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LifgUR3zkD
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.55/4.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.55/4.74  % Solved by: fo/fo7.sh
% 4.55/4.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.55/4.74  % done 5038 iterations in 4.288s
% 4.55/4.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.55/4.74  % SZS output start Refutation
% 4.55/4.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.55/4.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.55/4.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.55/4.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.55/4.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.55/4.74  thf(sk_A_type, type, sk_A: $i).
% 4.55/4.74  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 4.55/4.74  thf(sk_B_type, type, sk_B: $i).
% 4.55/4.74  thf(sk_D_3_type, type, sk_D_3: $i).
% 4.55/4.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.55/4.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.55/4.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.55/4.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.55/4.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.55/4.74  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 4.55/4.74  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.55/4.74  thf(t156_funct_1, conjecture,
% 4.55/4.74    (![A:$i,B:$i]:
% 4.55/4.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.55/4.74       ( ![C:$i]:
% 4.55/4.74         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.55/4.74           ( ![D:$i]:
% 4.55/4.74             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 4.55/4.74               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 4.55/4.74                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 4.55/4.74                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 4.55/4.74                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 4.55/4.74                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 4.55/4.74  thf(zf_stmt_0, negated_conjecture,
% 4.55/4.74    (~( ![A:$i,B:$i]:
% 4.55/4.74        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.55/4.74          ( ![C:$i]:
% 4.55/4.74            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.55/4.74              ( ![D:$i]:
% 4.55/4.74                ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 4.55/4.74                  ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 4.55/4.74                      ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 4.55/4.74                      ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 4.55/4.74                      ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 4.55/4.74                    ( ( C ) = ( D ) ) ) ) ) ) ) ) )),
% 4.55/4.74    inference('cnf.neg', [status(esa)], [t156_funct_1])).
% 4.55/4.74  thf('0', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf(d3_relat_1, axiom,
% 4.55/4.74    (![A:$i]:
% 4.55/4.74     ( ( v1_relat_1 @ A ) =>
% 4.55/4.74       ( ![B:$i]:
% 4.55/4.74         ( ( r1_tarski @ A @ B ) <=>
% 4.55/4.74           ( ![C:$i,D:$i]:
% 4.55/4.74             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 4.55/4.74               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 4.55/4.74  thf('1', plain,
% 4.55/4.74      (![X3 : $i, X4 : $i]:
% 4.55/4.74         ((r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X4)
% 4.55/4.74          | (r1_tarski @ X4 @ X3)
% 4.55/4.74          | ~ (v1_relat_1 @ X4))),
% 4.55/4.74      inference('cnf', [status(esa)], [d3_relat_1])).
% 4.55/4.74  thf(t20_relat_1, axiom,
% 4.55/4.74    (![A:$i,B:$i,C:$i]:
% 4.55/4.74     ( ( v1_relat_1 @ C ) =>
% 4.55/4.74       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 4.55/4.74         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 4.55/4.74           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 4.55/4.74  thf('2', plain,
% 4.55/4.74      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.55/4.74         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 4.55/4.74          | (r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 4.55/4.74          | ~ (v1_relat_1 @ X10))),
% 4.55/4.74      inference('cnf', [status(esa)], [t20_relat_1])).
% 4.55/4.74  thf('3', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X0)
% 4.55/4.74          | (r1_tarski @ X0 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X0)
% 4.55/4.74          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 4.55/4.74      inference('sup-', [status(thm)], ['1', '2'])).
% 4.55/4.74  thf('4', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 4.55/4.74          | (r1_tarski @ X0 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X0))),
% 4.55/4.74      inference('simplify', [status(thm)], ['3'])).
% 4.55/4.74  thf('5', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_C_2)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['0', '4'])).
% 4.55/4.74  thf('6', plain, ((v1_relat_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('7', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A) | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('demod', [status(thm)], ['5', '6'])).
% 4.55/4.74  thf('8', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf(d5_funct_1, axiom,
% 4.55/4.74    (![A:$i]:
% 4.55/4.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.55/4.74       ( ![B:$i]:
% 4.55/4.74         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 4.55/4.74           ( ![C:$i]:
% 4.55/4.74             ( ( r2_hidden @ C @ B ) <=>
% 4.55/4.74               ( ?[D:$i]:
% 4.55/4.74                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 4.55/4.74                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 4.55/4.74  thf('9', plain,
% 4.55/4.74      (![X12 : $i, X14 : $i, X15 : $i]:
% 4.55/4.74         (((X14) != (k2_relat_1 @ X12))
% 4.55/4.74          | (r2_hidden @ (sk_D_2 @ X15 @ X12) @ (k1_relat_1 @ X12))
% 4.55/4.74          | ~ (r2_hidden @ X15 @ X14)
% 4.55/4.74          | ~ (v1_funct_1 @ X12)
% 4.55/4.74          | ~ (v1_relat_1 @ X12))),
% 4.55/4.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.55/4.74  thf('10', plain,
% 4.55/4.74      (![X12 : $i, X15 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X12)
% 4.55/4.74          | ~ (v1_funct_1 @ X12)
% 4.55/4.74          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X12))
% 4.55/4.74          | (r2_hidden @ (sk_D_2 @ X15 @ X12) @ (k1_relat_1 @ X12)))),
% 4.55/4.74      inference('simplify', [status(thm)], ['9'])).
% 4.55/4.74  thf('11', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | (r2_hidden @ (sk_D_2 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 4.55/4.74          | ~ (v1_funct_1 @ sk_B)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_B))),
% 4.55/4.74      inference('sup-', [status(thm)], ['8', '10'])).
% 4.55/4.74  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('14', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | (r2_hidden @ (sk_D_2 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 4.55/4.74      inference('demod', [status(thm)], ['11', '12', '13'])).
% 4.55/4.74  thf('15', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B) @ 
% 4.55/4.74             (k1_relat_1 @ sk_B)))),
% 4.55/4.74      inference('sup-', [status(thm)], ['7', '14'])).
% 4.55/4.74  thf(t23_funct_1, axiom,
% 4.55/4.74    (![A:$i,B:$i]:
% 4.55/4.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.55/4.74       ( ![C:$i]:
% 4.55/4.74         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.55/4.74           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 4.55/4.74             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 4.55/4.74               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 4.55/4.74  thf('16', plain,
% 4.55/4.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X18)
% 4.55/4.74          | ~ (v1_funct_1 @ X18)
% 4.55/4.74          | ((k1_funct_1 @ (k5_relat_1 @ X19 @ X18) @ X20)
% 4.55/4.74              = (k1_funct_1 @ X18 @ (k1_funct_1 @ X19 @ X20)))
% 4.55/4.74          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 4.55/4.74          | ~ (v1_funct_1 @ X19)
% 4.55/4.74          | ~ (v1_relat_1 @ X19))),
% 4.55/4.74      inference('cnf', [status(esa)], [t23_funct_1])).
% 4.55/4.74  thf('17', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_B)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_B)
% 4.55/4.74          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X1) @ 
% 4.55/4.74              (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))
% 4.55/4.74              = (k1_funct_1 @ X1 @ 
% 4.55/4.74                 (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))))
% 4.55/4.74          | ~ (v1_funct_1 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X1))),
% 4.55/4.74      inference('sup-', [status(thm)], ['15', '16'])).
% 4.55/4.74  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('20', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X1) @ 
% 4.55/4.74              (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))
% 4.55/4.74              = (k1_funct_1 @ X1 @ 
% 4.55/4.74                 (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))))
% 4.55/4.74          | ~ (v1_funct_1 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X1))),
% 4.55/4.74      inference('demod', [status(thm)], ['17', '18', '19'])).
% 4.55/4.74  thf('21', plain,
% 4.55/4.74      (![X3 : $i, X4 : $i]:
% 4.55/4.74         ((r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X4)
% 4.55/4.74          | (r1_tarski @ X4 @ X3)
% 4.55/4.74          | ~ (v1_relat_1 @ X4))),
% 4.55/4.74      inference('cnf', [status(esa)], [d3_relat_1])).
% 4.55/4.74  thf(t8_funct_1, axiom,
% 4.55/4.74    (![A:$i,B:$i,C:$i]:
% 4.55/4.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.55/4.74       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 4.55/4.74         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 4.55/4.74           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 4.55/4.74  thf('22', plain,
% 4.55/4.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.55/4.74         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 4.55/4.74          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 4.55/4.74          | ~ (v1_funct_1 @ X22)
% 4.55/4.74          | ~ (v1_relat_1 @ X22))),
% 4.55/4.74      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.55/4.74  thf('23', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X0)
% 4.55/4.74          | (r1_tarski @ X0 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X0)
% 4.55/4.74          | ~ (v1_funct_1 @ X0)
% 4.55/4.74          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0))))),
% 4.55/4.74      inference('sup-', [status(thm)], ['21', '22'])).
% 4.55/4.74  thf('24', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 4.55/4.74          | ~ (v1_funct_1 @ X0)
% 4.55/4.74          | (r1_tarski @ X0 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X0))),
% 4.55/4.74      inference('simplify', [status(thm)], ['23'])).
% 4.55/4.74  thf('25', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A) | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('demod', [status(thm)], ['5', '6'])).
% 4.55/4.74  thf('26', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('27', plain,
% 4.55/4.74      (![X12 : $i, X14 : $i, X15 : $i]:
% 4.55/4.74         (((X14) != (k2_relat_1 @ X12))
% 4.55/4.74          | ((X15) = (k1_funct_1 @ X12 @ (sk_D_2 @ X15 @ X12)))
% 4.55/4.74          | ~ (r2_hidden @ X15 @ X14)
% 4.55/4.74          | ~ (v1_funct_1 @ X12)
% 4.55/4.74          | ~ (v1_relat_1 @ X12))),
% 4.55/4.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.55/4.74  thf('28', plain,
% 4.55/4.74      (![X12 : $i, X15 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X12)
% 4.55/4.74          | ~ (v1_funct_1 @ X12)
% 4.55/4.74          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X12))
% 4.55/4.74          | ((X15) = (k1_funct_1 @ X12 @ (sk_D_2 @ X15 @ X12))))),
% 4.55/4.74      inference('simplify', [status(thm)], ['27'])).
% 4.55/4.74  thf('29', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_2 @ X0 @ sk_B)))
% 4.55/4.74          | ~ (v1_funct_1 @ sk_B)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_B))),
% 4.55/4.74      inference('sup-', [status(thm)], ['26', '28'])).
% 4.55/4.74  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('32', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_2 @ X0 @ sk_B))))),
% 4.55/4.74      inference('demod', [status(thm)], ['29', '30', '31'])).
% 4.55/4.74  thf('33', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ((sk_C @ X0 @ sk_C_2)
% 4.55/4.74              = (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))))),
% 4.55/4.74      inference('sup-', [status(thm)], ['25', '32'])).
% 4.55/4.74  thf('34', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B) @ 
% 4.55/4.74             (k1_relat_1 @ sk_B)))),
% 4.55/4.74      inference('sup-', [status(thm)], ['7', '14'])).
% 4.55/4.74  thf('35', plain,
% 4.55/4.74      (![X12 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 4.55/4.74         (((X14) != (k2_relat_1 @ X12))
% 4.55/4.74          | (r2_hidden @ X16 @ X14)
% 4.55/4.74          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 4.55/4.74          | ((X16) != (k1_funct_1 @ X12 @ X17))
% 4.55/4.74          | ~ (v1_funct_1 @ X12)
% 4.55/4.74          | ~ (v1_relat_1 @ X12))),
% 4.55/4.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 4.55/4.74  thf('36', plain,
% 4.55/4.74      (![X12 : $i, X17 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X12)
% 4.55/4.74          | ~ (v1_funct_1 @ X12)
% 4.55/4.74          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 4.55/4.74          | (r2_hidden @ (k1_funct_1 @ X12 @ X17) @ (k2_relat_1 @ X12)))),
% 4.55/4.74      inference('simplify', [status(thm)], ['35'])).
% 4.55/4.74  thf('37', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74             (k2_relat_1 @ sk_B))
% 4.55/4.74          | ~ (v1_funct_1 @ sk_B)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_B))),
% 4.55/4.74      inference('sup-', [status(thm)], ['34', '36'])).
% 4.55/4.74  thf('38', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('41', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74             sk_A))),
% 4.55/4.74      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 4.55/4.74  thf('42', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('43', plain,
% 4.55/4.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 4.55/4.74          | ((X23) != (k1_funct_1 @ X22 @ X21))
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 4.55/4.74          | ~ (v1_funct_1 @ X22)
% 4.55/4.74          | ~ (v1_relat_1 @ X22))),
% 4.55/4.74      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.55/4.74  thf('44', plain,
% 4.55/4.74      (![X21 : $i, X22 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X22)
% 4.55/4.74          | ~ (v1_funct_1 @ X22)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X21 @ (k1_funct_1 @ X22 @ X21)) @ X22)
% 4.55/4.74          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 4.55/4.74      inference('simplify', [status(thm)], ['43'])).
% 4.55/4.74  thf('45', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_C_2)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_C_2))),
% 4.55/4.74      inference('sup-', [status(thm)], ['42', '44'])).
% 4.55/4.74  thf('46', plain, ((v1_funct_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('47', plain, ((v1_relat_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('48', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2))),
% 4.55/4.74      inference('demod', [status(thm)], ['45', '46', '47'])).
% 4.55/4.74  thf('49', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ 
% 4.55/4.74              (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74              (k1_funct_1 @ sk_C_2 @ 
% 4.55/4.74               (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))) @ 
% 4.55/4.74             sk_C_2))),
% 4.55/4.74      inference('sup-', [status(thm)], ['41', '48'])).
% 4.55/4.74  thf('50', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ 
% 4.55/4.74            (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74            (k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_C_2))) @ 
% 4.55/4.74           sk_C_2)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['33', '49'])).
% 4.55/4.74  thf('51', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ 
% 4.55/4.74              (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74              (k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_C_2))) @ 
% 4.55/4.74             sk_C_2))),
% 4.55/4.74      inference('simplify', [status(thm)], ['50'])).
% 4.55/4.74  thf('52', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ 
% 4.55/4.74            (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74            (sk_D @ X0 @ sk_C_2)) @ 
% 4.55/4.74           sk_C_2)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_C_2)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_C_2)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['24', '51'])).
% 4.55/4.74  thf('53', plain, ((v1_relat_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('54', plain, ((v1_funct_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('55', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ 
% 4.55/4.74            (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74            (sk_D @ X0 @ sk_C_2)) @ 
% 4.55/4.74           sk_C_2)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('demod', [status(thm)], ['52', '53', '54'])).
% 4.55/4.74  thf('56', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ 
% 4.55/4.74              (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74              (sk_D @ X0 @ sk_C_2)) @ 
% 4.55/4.74             sk_C_2))),
% 4.55/4.74      inference('simplify', [status(thm)], ['55'])).
% 4.55/4.74  thf('57', plain,
% 4.55/4.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.55/4.74         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 4.55/4.74          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 4.55/4.74          | ~ (v1_funct_1 @ X22)
% 4.55/4.74          | ~ (v1_relat_1 @ X22))),
% 4.55/4.74      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.55/4.74  thf('58', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_C_2)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_C_2)
% 4.55/4.74          | ((sk_D @ X0 @ sk_C_2)
% 4.55/4.74              = (k1_funct_1 @ sk_C_2 @ 
% 4.55/4.74                 (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))))),
% 4.55/4.74      inference('sup-', [status(thm)], ['56', '57'])).
% 4.55/4.74  thf('59', plain, ((v1_relat_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('60', plain, ((v1_funct_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('61', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ((sk_D @ X0 @ sk_C_2)
% 4.55/4.74              = (k1_funct_1 @ sk_C_2 @ 
% 4.55/4.74                 (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))))),
% 4.55/4.74      inference('demod', [status(thm)], ['58', '59', '60'])).
% 4.55/4.74  thf('62', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (((sk_D @ X0 @ sk_C_2)
% 4.55/4.74            = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 4.55/4.74               (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))
% 4.55/4.74          | ~ (v1_relat_1 @ sk_C_2)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_C_2)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['20', '61'])).
% 4.55/4.74  thf('63', plain, ((v1_relat_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('64', plain, ((v1_funct_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('65', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (((sk_D @ X0 @ sk_C_2)
% 4.55/4.74            = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 4.55/4.74               (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('demod', [status(thm)], ['62', '63', '64'])).
% 4.55/4.74  thf('66', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ((sk_D @ X0 @ sk_C_2)
% 4.55/4.74              = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 4.55/4.74                 (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))))),
% 4.55/4.74      inference('simplify', [status(thm)], ['65'])).
% 4.55/4.74  thf('67', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X1) @ 
% 4.55/4.74              (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))
% 4.55/4.74              = (k1_funct_1 @ X1 @ 
% 4.55/4.74                 (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))))
% 4.55/4.74          | ~ (v1_funct_1 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X1))),
% 4.55/4.74      inference('demod', [status(thm)], ['17', '18', '19'])).
% 4.55/4.74  thf('68', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | ((sk_C @ X0 @ sk_C_2)
% 4.55/4.74              = (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))))),
% 4.55/4.74      inference('sup-', [status(thm)], ['25', '32'])).
% 4.55/4.74  thf('69', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74             sk_A))),
% 4.55/4.74      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 4.55/4.74  thf('70', plain, (((k1_relat_1 @ sk_D_3) = (sk_A))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('71', plain,
% 4.55/4.74      (![X21 : $i, X22 : $i]:
% 4.55/4.74         (~ (v1_relat_1 @ X22)
% 4.55/4.74          | ~ (v1_funct_1 @ X22)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X21 @ (k1_funct_1 @ X22 @ X21)) @ X22)
% 4.55/4.74          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 4.55/4.74      inference('simplify', [status(thm)], ['43'])).
% 4.55/4.74  thf('72', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_3 @ X0)) @ sk_D_3)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_D_3)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_D_3))),
% 4.55/4.74      inference('sup-', [status(thm)], ['70', '71'])).
% 4.55/4.74  thf('73', plain, ((v1_funct_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('74', plain, ((v1_relat_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('75', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_3 @ X0)) @ sk_D_3))),
% 4.55/4.74      inference('demod', [status(thm)], ['72', '73', '74'])).
% 4.55/4.74  thf('76', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ 
% 4.55/4.74              (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)) @ 
% 4.55/4.74              (k1_funct_1 @ sk_D_3 @ 
% 4.55/4.74               (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))) @ 
% 4.55/4.74             sk_D_3))),
% 4.55/4.74      inference('sup-', [status(thm)], ['69', '75'])).
% 4.55/4.74  thf('77', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ (sk_C @ X0 @ sk_C_2) @ 
% 4.55/4.74            (k1_funct_1 @ sk_D_3 @ 
% 4.55/4.74             (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))) @ 
% 4.55/4.74           sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['68', '76'])).
% 4.55/4.74  thf('78', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_C_2) @ 
% 4.55/4.74              (k1_funct_1 @ sk_D_3 @ 
% 4.55/4.74               (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B)))) @ 
% 4.55/4.74             sk_D_3))),
% 4.55/4.74      inference('simplify', [status(thm)], ['77'])).
% 4.55/4.74  thf('79', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ (sk_C @ X0 @ sk_C_2) @ 
% 4.55/4.74            (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_D_3) @ 
% 4.55/4.74             (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))) @ 
% 4.55/4.74           sk_D_3)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_D_3)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['67', '78'])).
% 4.55/4.74  thf('80', plain,
% 4.55/4.74      (((k5_relat_1 @ sk_B @ sk_C_2) = (k5_relat_1 @ sk_B @ sk_D_3))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('81', plain, ((v1_relat_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('82', plain, ((v1_funct_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('83', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ (sk_C @ X0 @ sk_C_2) @ 
% 4.55/4.74            (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 4.55/4.74             (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))) @ 
% 4.55/4.74           sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 4.55/4.74  thf('84', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_C_2) @ 
% 4.55/4.74              (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 4.55/4.74               (sk_D_2 @ (sk_C @ X0 @ sk_C_2) @ sk_B))) @ 
% 4.55/4.74             sk_D_3))),
% 4.55/4.74      inference('simplify', [status(thm)], ['83'])).
% 4.55/4.74  thf('85', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ (sk_C @ X0 @ sk_C_2) @ (sk_D @ X0 @ sk_C_2)) @ sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_C_2 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['66', '84'])).
% 4.55/4.74  thf('86', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_C_2 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_C_2) @ (sk_D @ X0 @ sk_C_2)) @ sk_D_3))),
% 4.55/4.74      inference('simplify', [status(thm)], ['85'])).
% 4.55/4.74  thf('87', plain,
% 4.55/4.74      (![X3 : $i, X4 : $i]:
% 4.55/4.74         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X3)
% 4.55/4.74          | (r1_tarski @ X4 @ X3)
% 4.55/4.74          | ~ (v1_relat_1 @ X4))),
% 4.55/4.74      inference('cnf', [status(esa)], [d3_relat_1])).
% 4.55/4.74  thf('88', plain,
% 4.55/4.74      (((r1_tarski @ sk_C_2 @ sk_D_3)
% 4.55/4.74        | ~ (v1_relat_1 @ sk_C_2)
% 4.55/4.74        | (r1_tarski @ sk_C_2 @ sk_D_3))),
% 4.55/4.74      inference('sup-', [status(thm)], ['86', '87'])).
% 4.55/4.74  thf('89', plain, ((v1_relat_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('90', plain,
% 4.55/4.74      (((r1_tarski @ sk_C_2 @ sk_D_3) | (r1_tarski @ sk_C_2 @ sk_D_3))),
% 4.55/4.74      inference('demod', [status(thm)], ['88', '89'])).
% 4.55/4.74  thf('91', plain, ((r1_tarski @ sk_C_2 @ sk_D_3)),
% 4.55/4.74      inference('simplify', [status(thm)], ['90'])).
% 4.55/4.74  thf(d10_xboole_0, axiom,
% 4.55/4.74    (![A:$i,B:$i]:
% 4.55/4.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.55/4.74  thf('92', plain,
% 4.55/4.74      (![X0 : $i, X2 : $i]:
% 4.55/4.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.55/4.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.55/4.74  thf('93', plain, ((~ (r1_tarski @ sk_D_3 @ sk_C_2) | ((sk_D_3) = (sk_C_2)))),
% 4.55/4.74      inference('sup-', [status(thm)], ['91', '92'])).
% 4.55/4.74  thf('94', plain, (((sk_C_2) != (sk_D_3))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('95', plain, (~ (r1_tarski @ sk_D_3 @ sk_C_2)),
% 4.55/4.74      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 4.55/4.74  thf('96', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 4.55/4.74          | ~ (v1_funct_1 @ X0)
% 4.55/4.74          | (r1_tarski @ X0 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X0))),
% 4.55/4.74      inference('simplify', [status(thm)], ['23'])).
% 4.55/4.74  thf('97', plain, ((r1_tarski @ sk_C_2 @ sk_D_3)),
% 4.55/4.74      inference('simplify', [status(thm)], ['90'])).
% 4.55/4.74  thf('98', plain, (((k1_relat_1 @ sk_D_3) = (sk_A))),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('99', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 4.55/4.74          | (r1_tarski @ X0 @ X1)
% 4.55/4.74          | ~ (v1_relat_1 @ X0))),
% 4.55/4.74      inference('simplify', [status(thm)], ['3'])).
% 4.55/4.74  thf('100', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ (sk_C @ X0 @ sk_D_3) @ sk_A)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['98', '99'])).
% 4.55/4.74  thf('101', plain, ((v1_relat_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('102', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ (sk_C @ X0 @ sk_D_3) @ sk_A) | (r1_tarski @ sk_D_3 @ X0))),
% 4.55/4.74      inference('demod', [status(thm)], ['100', '101'])).
% 4.55/4.74  thf('103', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (~ (r2_hidden @ X0 @ sk_A)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2))),
% 4.55/4.74      inference('demod', [status(thm)], ['45', '46', '47'])).
% 4.55/4.74  thf('104', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_D_3) @ 
% 4.55/4.74              (k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))) @ 
% 4.55/4.74             sk_C_2))),
% 4.55/4.74      inference('sup-', [status(thm)], ['102', '103'])).
% 4.55/4.74  thf('105', plain,
% 4.55/4.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 4.55/4.74         (~ (r1_tarski @ X4 @ X5)
% 4.55/4.74          | (r2_hidden @ (k4_tarski @ X6 @ X7) @ X5)
% 4.55/4.74          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X4)
% 4.55/4.74          | ~ (v1_relat_1 @ X4))),
% 4.55/4.74      inference('cnf', [status(esa)], [d3_relat_1])).
% 4.55/4.74  thf('106', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_C_2)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_D_3) @ 
% 4.55/4.74              (k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))) @ 
% 4.55/4.74             X1)
% 4.55/4.74          | ~ (r1_tarski @ sk_C_2 @ X1))),
% 4.55/4.74      inference('sup-', [status(thm)], ['104', '105'])).
% 4.55/4.74  thf('107', plain, ((v1_relat_1 @ sk_C_2)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('108', plain,
% 4.55/4.74      (![X0 : $i, X1 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_D_3) @ 
% 4.55/4.74              (k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))) @ 
% 4.55/4.74             X1)
% 4.55/4.74          | ~ (r1_tarski @ sk_C_2 @ X1))),
% 4.55/4.74      inference('demod', [status(thm)], ['106', '107'])).
% 4.55/4.74  thf('109', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ (sk_C @ X0 @ sk_D_3) @ 
% 4.55/4.74            (k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))) @ 
% 4.55/4.74           sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0))),
% 4.55/4.74      inference('sup-', [status(thm)], ['97', '108'])).
% 4.55/4.74  thf('110', plain,
% 4.55/4.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.55/4.74         (~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 4.55/4.74          | ((X23) = (k1_funct_1 @ X22 @ X21))
% 4.55/4.74          | ~ (v1_funct_1 @ X22)
% 4.55/4.74          | ~ (v1_relat_1 @ X22))),
% 4.55/4.74      inference('cnf', [status(esa)], [t8_funct_1])).
% 4.55/4.74  thf('111', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | ~ (v1_relat_1 @ sk_D_3)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_D_3)
% 4.55/4.74          | ((k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))
% 4.55/4.74              = (k1_funct_1 @ sk_D_3 @ (sk_C @ X0 @ sk_D_3))))),
% 4.55/4.74      inference('sup-', [status(thm)], ['109', '110'])).
% 4.55/4.74  thf('112', plain, ((v1_relat_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('113', plain, ((v1_funct_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('114', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | ((k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))
% 4.55/4.74              = (k1_funct_1 @ sk_D_3 @ (sk_C @ X0 @ sk_D_3))))),
% 4.55/4.74      inference('demod', [status(thm)], ['111', '112', '113'])).
% 4.55/4.74  thf('115', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (((k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3)) = (sk_D @ X0 @ sk_D_3))
% 4.55/4.74          | ~ (v1_relat_1 @ sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | ~ (v1_funct_1 @ sk_D_3)
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['96', '114'])).
% 4.55/4.74  thf('116', plain, ((v1_relat_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('117', plain, ((v1_funct_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('118', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         (((k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3)) = (sk_D @ X0 @ sk_D_3))
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0))),
% 4.55/4.74      inference('demod', [status(thm)], ['115', '116', '117'])).
% 4.55/4.74  thf('119', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | ((k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))
% 4.55/4.74              = (sk_D @ X0 @ sk_D_3)))),
% 4.55/4.74      inference('simplify', [status(thm)], ['118'])).
% 4.55/4.74  thf('120', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_D_3) @ 
% 4.55/4.74              (k1_funct_1 @ sk_C_2 @ (sk_C @ X0 @ sk_D_3))) @ 
% 4.55/4.74             sk_C_2))),
% 4.55/4.74      inference('sup-', [status(thm)], ['102', '103'])).
% 4.55/4.74  thf('121', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r2_hidden @ 
% 4.55/4.74           (k4_tarski @ (sk_C @ X0 @ sk_D_3) @ (sk_D @ X0 @ sk_D_3)) @ sk_C_2)
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | (r1_tarski @ sk_D_3 @ X0))),
% 4.55/4.74      inference('sup+', [status(thm)], ['119', '120'])).
% 4.55/4.74  thf('122', plain,
% 4.55/4.74      (![X0 : $i]:
% 4.55/4.74         ((r1_tarski @ sk_D_3 @ X0)
% 4.55/4.74          | (r2_hidden @ 
% 4.55/4.74             (k4_tarski @ (sk_C @ X0 @ sk_D_3) @ (sk_D @ X0 @ sk_D_3)) @ sk_C_2))),
% 4.55/4.74      inference('simplify', [status(thm)], ['121'])).
% 4.55/4.74  thf('123', plain,
% 4.55/4.74      (![X3 : $i, X4 : $i]:
% 4.55/4.74         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_D @ X3 @ X4)) @ X3)
% 4.55/4.74          | (r1_tarski @ X4 @ X3)
% 4.55/4.74          | ~ (v1_relat_1 @ X4))),
% 4.55/4.74      inference('cnf', [status(esa)], [d3_relat_1])).
% 4.55/4.74  thf('124', plain,
% 4.55/4.74      (((r1_tarski @ sk_D_3 @ sk_C_2)
% 4.55/4.74        | ~ (v1_relat_1 @ sk_D_3)
% 4.55/4.74        | (r1_tarski @ sk_D_3 @ sk_C_2))),
% 4.55/4.74      inference('sup-', [status(thm)], ['122', '123'])).
% 4.55/4.74  thf('125', plain, ((v1_relat_1 @ sk_D_3)),
% 4.55/4.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.74  thf('126', plain,
% 4.55/4.74      (((r1_tarski @ sk_D_3 @ sk_C_2) | (r1_tarski @ sk_D_3 @ sk_C_2))),
% 4.55/4.74      inference('demod', [status(thm)], ['124', '125'])).
% 4.55/4.74  thf('127', plain, ((r1_tarski @ sk_D_3 @ sk_C_2)),
% 4.55/4.74      inference('simplify', [status(thm)], ['126'])).
% 4.55/4.74  thf('128', plain, ($false), inference('demod', [status(thm)], ['95', '127'])).
% 4.55/4.74  
% 4.55/4.74  % SZS output end Refutation
% 4.55/4.74  
% 4.55/4.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
