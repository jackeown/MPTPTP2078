%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.upyqHZOyHg

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:41 EST 2020

% Result     : Theorem 9.87s
% Output     : Refutation 9.87s
% Verified   : 
% Statistics : Number of formulae       :  236 (1416 expanded)
%              Number of leaves         :   25 ( 385 expanded)
%              Depth                    :   43
%              Number of atoms          : 2770 (26221 expanded)
%              Number of equality atoms :  107 (2577 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_5_type,type,(
    sk_D_5: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X8 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X8 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

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

thf('8',plain,(
    ! [X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( X24
       != ( k1_funct_1 @ X20 @ X25 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('9',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( X23
        = ( k1_funct_1 @ X20 @ ( sk_D_4 @ X23 @ X20 ) ) )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('13',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X20 ) )
      | ( X23
        = ( k1_funct_1 @ X20 @ ( sk_D_4 @ X23 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('18',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ ( sk_D_4 @ X23 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('19',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ ( sk_D_4 @ X23 @ X20 ) @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D_2 @ X16 @ X14 ) ) @ X14 )
      | ( X15
       != ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('23',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D_2 @ X16 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( sk_D_2 @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( sk_D_2 @ ( sk_D_4 @ ( sk_D @ X1 @ X0 ) @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( sk_D_2 @ ( sk_D_4 @ ( sk_D @ X1 @ X0 ) @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D_2 @ ( sk_D_4 @ ( sk_D @ X1 @ X0 ) @ X0 ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_2 @ ( sk_D_4 @ ( sk_D @ X1 @ X0 ) @ X0 ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_2 @ ( sk_D_4 @ ( sk_D @ X1 @ X0 ) @ X0 ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( ( sk_D_2 @ ( sk_D_4 @ ( sk_D @ X1 @ X0 ) @ X0 ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( sk_D_2 @ ( sk_D_4 @ ( sk_D @ X1 @ X0 ) @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_4 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('41',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D_2 @ X16 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_D_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

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

thf('46',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_A )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_A )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X20 ) )
      | ( X23
        = ( k1_funct_1 @ X20 @ ( sk_D_4 @ X23 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_4 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_4 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_C_1 @ X0 @ sk_C_4 )
        = ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_A )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('59',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ ( sk_D_4 @ X23 @ X20 ) @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_4 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_4 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D_2 @ X16 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ X0 @ sk_C_4 ) ) @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ ( sk_D_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_C_4 ) ) @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_4 )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ( ( sk_D_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ X0 ) @ ( k2_relat_1 @ sk_C_4 ) )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ X0 ) @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) @ ( k2_relat_1 @ sk_C_4 ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X20 ) )
      | ( X23
        = ( k1_funct_1 @ X20 @ ( sk_D_4 @ X23 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( sk_D_4 @ ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) @ sk_C_4 ) ) )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( sk_D_4 @ ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) @ sk_C_4 ) ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( sk_D_4 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) ) @ sk_C_4 ) ) )
      | ~ ( v1_relat_1 @ sk_C_4 )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( sk_D_4 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) ) @ sk_C_4 ) ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( sk_D_4 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) ) @ sk_C_4 ) ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( sk_D @ X0 @ sk_C_4 ) )
      | ~ ( v1_relat_1 @ sk_C_4 )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( sk_D @ X0 @ sk_C_4 ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( sk_D @ X0 @ sk_C_4 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_A )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_D_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D_2 @ X16 @ X14 ) ) @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ X0 @ sk_D_5 ) ) @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_4 ) @ ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 ) ) @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_5 )
      | ~ ( v1_funct_1 @ sk_D_5 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_C_4 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_C_4 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

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

thf('119',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k1_funct_1 @ X26 @ ( k1_funct_1 @ X27 @ X28 ) ) )
      | ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X1 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X1 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ sk_C_4 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_4 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_C_4 )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_4 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_4 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X1 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_C_1 @ X0 @ sk_C_4 )
        = ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ X0 @ sk_D_5 ) ) @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ ( sk_D_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_D_5 ) ) @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_5 )
      | ~ ( v1_funct_1 @ sk_D_5 )
      | ( ( sk_D_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_D_5 )
        = ( k1_funct_1 @ sk_D_5 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) @ sk_D_5 )
        = ( k1_funct_1 @ sk_D_5 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( k1_funct_1 @ sk_D_5 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( k1_funct_1 @ sk_D_5 @ ( k1_funct_1 @ sk_B @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_D_5 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_D_5 )
      | ~ ( v1_funct_1 @ sk_D_5 )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','141'])).

thf('143',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_4 )
    = ( k5_relat_1 @ sk_B @ sk_D_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_4 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_4 ) @ ( sk_D_4 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_D_5 )
        = ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_C_4 ) )
        = ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_C_4 ) )
        = ( sk_D_2 @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_C_4 ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_C_4 ) )
        = ( sk_D @ X0 @ sk_C_4 ) )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_C_4 ) )
        = ( sk_D @ X0 @ sk_C_4 ) ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_4 ) @ sk_A )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_D_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( X31
       != ( k1_funct_1 @ X30 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('157',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( r2_hidden @ ( k4_tarski @ X29 @ ( k1_funct_1 @ X30 @ X29 ) ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_5 @ X0 ) ) @ sk_D_5 )
      | ~ ( v1_funct_1 @ sk_D_5 )
      | ~ ( v1_relat_1 @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['155','157'])).

thf('159',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_5 @ X0 ) ) @ sk_D_5 ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_4 ) @ ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_C_4 ) ) ) @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['154','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_4 ) @ ( sk_D @ X0 @ sk_C_4 ) ) @ sk_D_5 )
      | ( r1_tarski @ sk_C_4 @ X0 )
      | ( r1_tarski @ sk_C_4 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_4 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_4 ) @ ( sk_D @ X0 @ sk_C_4 ) ) @ sk_D_5 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X7 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('166',plain,
    ( ( r1_tarski @ sk_C_4 @ sk_D_5 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r1_tarski @ sk_C_4 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( r1_tarski @ sk_C_4 @ sk_D_5 )
    | ( r1_tarski @ sk_C_4 @ sk_D_5 ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    r1_tarski @ sk_C_4 @ sk_D_5 ),
    inference(simplify,[status(thm)],['168'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('170',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('171',plain,
    ( ~ ( r1_tarski @ sk_D_5 @ sk_C_4 )
    | ( sk_D_5 = sk_C_4 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    sk_C_4 != sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ~ ( r1_tarski @ sk_D_5 @ sk_C_4 ) ),
    inference('simplify_reflect-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('175',plain,
    ( ( k1_relat_1 @ sk_D_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D_5 ) @ sk_A )
      | ( r1_tarski @ sk_D_5 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_5 ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D_5 ) @ sk_A )
      | ( r1_tarski @ sk_D_5 @ X0 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( r2_hidden @ ( k4_tarski @ X29 @ ( k1_funct_1 @ X30 @ X29 ) ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_4 @ X0 ) ) @ sk_C_4 )
      | ~ ( v1_funct_1 @ sk_C_4 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_4 @ X0 ) ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_5 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_D_5 ) @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) ) ) @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['179','185'])).

thf('187',plain,(
    r1_tarski @ sk_C_4 @ sk_D_5 ),
    inference(simplify,[status(thm)],['168'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_5 )
      | ~ ( r2_hidden @ X0 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_5 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_D_5 ) @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) ) ) @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_5 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_5 )
      | ~ ( v1_funct_1 @ sk_D_5 )
      | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) )
        = ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_D_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_5 @ X0 )
      | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) )
        = ( k1_funct_1 @ sk_D_5 @ ( sk_C_1 @ X0 @ sk_D_5 ) ) ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) )
        = ( sk_D @ X0 @ sk_D_5 ) )
      | ~ ( v1_relat_1 @ sk_D_5 )
      | ( r1_tarski @ sk_D_5 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_5 )
      | ( r1_tarski @ sk_D_5 @ X0 ) ) ),
    inference('sup+',[status(thm)],['174','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) )
        = ( sk_D @ X0 @ sk_D_5 ) )
      | ( r1_tarski @ sk_D_5 @ X0 )
      | ( r1_tarski @ sk_D_5 @ X0 ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_5 @ X0 )
      | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) )
        = ( sk_D @ X0 @ sk_D_5 ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_5 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_D_5 ) @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_1 @ X0 @ sk_D_5 ) ) ) @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['179','185'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_D_5 ) @ ( sk_D @ X0 @ sk_D_5 ) ) @ sk_C_4 )
      | ( r1_tarski @ sk_D_5 @ X0 )
      | ( r1_tarski @ sk_D_5 @ X0 ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_5 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_D_5 ) @ ( sk_D @ X0 @ sk_D_5 ) ) @ sk_C_4 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X7 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('205',plain,
    ( ( r1_tarski @ sk_D_5 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_D_5 )
    | ( r1_tarski @ sk_D_5 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( r1_tarski @ sk_D_5 @ sk_C_4 )
    | ( r1_tarski @ sk_D_5 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    r1_tarski @ sk_D_5 @ sk_C_4 ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    $false ),
    inference(demod,[status(thm)],['173','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.upyqHZOyHg
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.87/10.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.87/10.14  % Solved by: fo/fo7.sh
% 9.87/10.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.87/10.14  % done 9903 iterations in 9.673s
% 9.87/10.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.87/10.14  % SZS output start Refutation
% 9.87/10.14  thf(sk_B_type, type, sk_B: $i).
% 9.87/10.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.87/10.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.87/10.14  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 9.87/10.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.87/10.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 9.87/10.14  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 9.87/10.14  thf(sk_D_5_type, type, sk_D_5: $i).
% 9.87/10.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.87/10.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.87/10.14  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 9.87/10.14  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 9.87/10.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.87/10.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.87/10.14  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 9.87/10.14  thf(sk_A_type, type, sk_A: $i).
% 9.87/10.14  thf(sk_C_4_type, type, sk_C_4: $i).
% 9.87/10.14  thf(d3_relat_1, axiom,
% 9.87/10.14    (![A:$i]:
% 9.87/10.14     ( ( v1_relat_1 @ A ) =>
% 9.87/10.14       ( ![B:$i]:
% 9.87/10.14         ( ( r1_tarski @ A @ B ) <=>
% 9.87/10.14           ( ![C:$i,D:$i]:
% 9.87/10.14             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 9.87/10.14               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 9.87/10.14  thf('0', plain,
% 9.87/10.14      (![X7 : $i, X8 : $i]:
% 9.87/10.14         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ X8)
% 9.87/10.14          | (r1_tarski @ X8 @ X7)
% 9.87/10.14          | ~ (v1_relat_1 @ X8))),
% 9.87/10.14      inference('cnf', [status(esa)], [d3_relat_1])).
% 9.87/10.14  thf(t8_funct_1, axiom,
% 9.87/10.14    (![A:$i,B:$i,C:$i]:
% 9.87/10.14     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.87/10.14       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 9.87/10.14         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 9.87/10.14           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 9.87/10.14  thf('1', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('2', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['0', '1'])).
% 9.87/10.14  thf('3', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['2'])).
% 9.87/10.14  thf('4', plain,
% 9.87/10.14      (![X7 : $i, X8 : $i]:
% 9.87/10.14         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ X8)
% 9.87/10.14          | (r1_tarski @ X8 @ X7)
% 9.87/10.14          | ~ (v1_relat_1 @ X8))),
% 9.87/10.14      inference('cnf', [status(esa)], [d3_relat_1])).
% 9.87/10.14  thf(d4_relat_1, axiom,
% 9.87/10.14    (![A:$i,B:$i]:
% 9.87/10.14     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 9.87/10.14       ( ![C:$i]:
% 9.87/10.14         ( ( r2_hidden @ C @ B ) <=>
% 9.87/10.14           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 9.87/10.14  thf('5', plain,
% 9.87/10.14      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 9.87/10.14          | (r2_hidden @ X12 @ X15)
% 9.87/10.14          | ((X15) != (k1_relat_1 @ X14)))),
% 9.87/10.14      inference('cnf', [status(esa)], [d4_relat_1])).
% 9.87/10.14  thf('6', plain,
% 9.87/10.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.87/10.14         ((r2_hidden @ X12 @ (k1_relat_1 @ X14))
% 9.87/10.14          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14))),
% 9.87/10.14      inference('simplify', [status(thm)], ['5'])).
% 9.87/10.14  thf('7', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['4', '6'])).
% 9.87/10.14  thf(d5_funct_1, axiom,
% 9.87/10.14    (![A:$i]:
% 9.87/10.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.87/10.14       ( ![B:$i]:
% 9.87/10.14         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 9.87/10.14           ( ![C:$i]:
% 9.87/10.14             ( ( r2_hidden @ C @ B ) <=>
% 9.87/10.14               ( ?[D:$i]:
% 9.87/10.14                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 9.87/10.14                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 9.87/10.14  thf('8', plain,
% 9.87/10.14      (![X20 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 9.87/10.14         (((X22) != (k2_relat_1 @ X20))
% 9.87/10.14          | (r2_hidden @ X24 @ X22)
% 9.87/10.14          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 9.87/10.14          | ((X24) != (k1_funct_1 @ X20 @ X25))
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (v1_relat_1 @ X20))),
% 9.87/10.14      inference('cnf', [status(esa)], [d5_funct_1])).
% 9.87/10.14  thf('9', plain,
% 9.87/10.14      (![X20 : $i, X25 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['8'])).
% 9.87/10.14  thf('10', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 9.87/10.14             (k2_relat_1 @ X0))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('sup-', [status(thm)], ['7', '9'])).
% 9.87/10.14  thf('11', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 9.87/10.14             (k2_relat_1 @ X0))
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1))),
% 9.87/10.14      inference('simplify', [status(thm)], ['10'])).
% 9.87/10.14  thf('12', plain,
% 9.87/10.14      (![X20 : $i, X22 : $i, X23 : $i]:
% 9.87/10.14         (((X22) != (k2_relat_1 @ X20))
% 9.87/10.14          | ((X23) = (k1_funct_1 @ X20 @ (sk_D_4 @ X23 @ X20)))
% 9.87/10.14          | ~ (r2_hidden @ X23 @ X22)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (v1_relat_1 @ X20))),
% 9.87/10.14      inference('cnf', [status(esa)], [d5_funct_1])).
% 9.87/10.14  thf('13', plain,
% 9.87/10.14      (![X20 : $i, X23 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X20))
% 9.87/10.14          | ((X23) = (k1_funct_1 @ X20 @ (sk_D_4 @ X23 @ X20))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['12'])).
% 9.87/10.14  thf('14', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ((k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))
% 9.87/10.14              = (k1_funct_1 @ X0 @ 
% 9.87/10.14                 (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('sup-', [status(thm)], ['11', '13'])).
% 9.87/10.14  thf('15', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))
% 9.87/10.14            = (k1_funct_1 @ X0 @ 
% 9.87/10.14               (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1))),
% 9.87/10.14      inference('simplify', [status(thm)], ['14'])).
% 9.87/10.14  thf('16', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['2'])).
% 9.87/10.14  thf('17', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 9.87/10.14             (k2_relat_1 @ X0))
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1))),
% 9.87/10.14      inference('simplify', [status(thm)], ['10'])).
% 9.87/10.14  thf('18', plain,
% 9.87/10.14      (![X20 : $i, X22 : $i, X23 : $i]:
% 9.87/10.14         (((X22) != (k2_relat_1 @ X20))
% 9.87/10.14          | (r2_hidden @ (sk_D_4 @ X23 @ X20) @ (k1_relat_1 @ X20))
% 9.87/10.14          | ~ (r2_hidden @ X23 @ X22)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (v1_relat_1 @ X20))),
% 9.87/10.14      inference('cnf', [status(esa)], [d5_funct_1])).
% 9.87/10.14  thf('19', plain,
% 9.87/10.14      (![X20 : $i, X23 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X20))
% 9.87/10.14          | (r2_hidden @ (sk_D_4 @ X23 @ X20) @ (k1_relat_1 @ X20)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['18'])).
% 9.87/10.14  thf('20', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14             (k1_relat_1 @ X0))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('sup-', [status(thm)], ['17', '19'])).
% 9.87/10.14  thf('21', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r2_hidden @ 
% 9.87/10.14           (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14           (k1_relat_1 @ X0))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1))),
% 9.87/10.14      inference('simplify', [status(thm)], ['20'])).
% 9.87/10.14  thf('22', plain,
% 9.87/10.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X16 @ X15)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X16 @ (sk_D_2 @ X16 @ X14)) @ X14)
% 9.87/10.14          | ((X15) != (k1_relat_1 @ X14)))),
% 9.87/10.14      inference('cnf', [status(esa)], [d4_relat_1])).
% 9.87/10.14  thf('23', plain,
% 9.87/10.14      (![X14 : $i, X16 : $i]:
% 9.87/10.14         ((r2_hidden @ (k4_tarski @ X16 @ (sk_D_2 @ X16 @ X14)) @ X14)
% 9.87/10.14          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['22'])).
% 9.87/10.14  thf('24', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ 
% 9.87/10.14              (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14              (sk_D_2 @ 
% 9.87/10.14               (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ X0)) @ 
% 9.87/10.14             X0))),
% 9.87/10.14      inference('sup-', [status(thm)], ['21', '23'])).
% 9.87/10.14  thf('25', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r2_hidden @ 
% 9.87/10.14           (k4_tarski @ 
% 9.87/10.14            (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14            (sk_D_2 @ (sk_D_4 @ (sk_D @ X1 @ X0) @ X0) @ X0)) @ 
% 9.87/10.14           X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1))),
% 9.87/10.14      inference('sup+', [status(thm)], ['16', '24'])).
% 9.87/10.14  thf('26', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ 
% 9.87/10.14              (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14              (sk_D_2 @ (sk_D_4 @ (sk_D @ X1 @ X0) @ X0) @ X0)) @ 
% 9.87/10.14             X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['25'])).
% 9.87/10.14  thf('27', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('28', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_D_4 @ (sk_D @ X1 @ X0) @ X0) @ X0)
% 9.87/10.14              = (k1_funct_1 @ X0 @ 
% 9.87/10.14                 (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['26', '27'])).
% 9.87/10.14  thf('29', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_D_4 @ (sk_D @ X1 @ X0) @ X0) @ X0)
% 9.87/10.14            = (k1_funct_1 @ X0 @ 
% 9.87/10.14               (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['28'])).
% 9.87/10.14  thf('30', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_D_4 @ (sk_D @ X1 @ X0) @ X0) @ X0)
% 9.87/10.14            = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_funct_1 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['15', '29'])).
% 9.87/10.14  thf('31', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ((sk_D_2 @ (sk_D_4 @ (sk_D @ X1 @ X0) @ X0) @ X0)
% 9.87/10.14              = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['30'])).
% 9.87/10.14  thf('32', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ 
% 9.87/10.14              (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14              (sk_D_2 @ (sk_D_4 @ (sk_D @ X1 @ X0) @ X0) @ X0)) @ 
% 9.87/10.14             X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['25'])).
% 9.87/10.14  thf('33', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r2_hidden @ 
% 9.87/10.14           (k4_tarski @ 
% 9.87/10.14            (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14            (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))) @ 
% 9.87/10.14           X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_funct_1 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['31', '32'])).
% 9.87/10.14  thf('34', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ 
% 9.87/10.14              (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14              (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))) @ 
% 9.87/10.14             X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['33'])).
% 9.87/10.14  thf('35', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r2_hidden @ 
% 9.87/10.14           (k4_tarski @ 
% 9.87/10.14            (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14            (sk_D @ X1 @ X0)) @ 
% 9.87/10.14           X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['3', '34'])).
% 9.87/10.14  thf('36', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ 
% 9.87/10.14              (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0) @ 
% 9.87/10.14              (sk_D @ X1 @ X0)) @ 
% 9.87/10.14             X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['35'])).
% 9.87/10.14  thf('37', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('38', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ((sk_D @ X1 @ X0)
% 9.87/10.14              = (k1_funct_1 @ X0 @ 
% 9.87/10.14                 (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['36', '37'])).
% 9.87/10.14  thf('39', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((sk_D @ X1 @ X0)
% 9.87/10.14            = (k1_funct_1 @ X0 @ 
% 9.87/10.14               (sk_D_4 @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['38'])).
% 9.87/10.14  thf('40', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['4', '6'])).
% 9.87/10.14  thf('41', plain,
% 9.87/10.14      (![X14 : $i, X16 : $i]:
% 9.87/10.14         ((r2_hidden @ (k4_tarski @ X16 @ (sk_D_2 @ X16 @ X14)) @ X14)
% 9.87/10.14          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['22'])).
% 9.87/10.14  thf('42', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X1 @ X0) @ 
% 9.87/10.14              (sk_D_2 @ (sk_C_1 @ X1 @ X0) @ X0)) @ 
% 9.87/10.14             X0))),
% 9.87/10.14      inference('sup-', [status(thm)], ['40', '41'])).
% 9.87/10.14  thf('43', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('44', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X1 @ X0) @ X0)
% 9.87/10.14              = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['42', '43'])).
% 9.87/10.14  thf('45', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X1 @ X0) @ X0)
% 9.87/10.14            = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['44'])).
% 9.87/10.14  thf(t156_funct_1, conjecture,
% 9.87/10.14    (![A:$i,B:$i]:
% 9.87/10.14     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.87/10.14       ( ![C:$i]:
% 9.87/10.14         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.87/10.14           ( ![D:$i]:
% 9.87/10.14             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 9.87/10.14               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 9.87/10.14                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 9.87/10.14                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 9.87/10.14                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 9.87/10.14                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 9.87/10.14  thf(zf_stmt_0, negated_conjecture,
% 9.87/10.14    (~( ![A:$i,B:$i]:
% 9.87/10.14        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.87/10.14          ( ![C:$i]:
% 9.87/10.14            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.87/10.14              ( ![D:$i]:
% 9.87/10.14                ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 9.87/10.14                  ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 9.87/10.14                      ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 9.87/10.14                      ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 9.87/10.14                      ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 9.87/10.14                    ( ( C ) = ( D ) ) ) ) ) ) ) ) )),
% 9.87/10.14    inference('cnf.neg', [status(esa)], [t156_funct_1])).
% 9.87/10.14  thf('46', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('47', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['4', '6'])).
% 9.87/10.14  thf('48', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_4) @ sk_A)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4))),
% 9.87/10.14      inference('sup+', [status(thm)], ['46', '47'])).
% 9.87/10.14  thf('49', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('50', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_4) @ sk_A)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['48', '49'])).
% 9.87/10.14  thf('51', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('52', plain,
% 9.87/10.14      (![X20 : $i, X23 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X20))
% 9.87/10.14          | ((X23) = (k1_funct_1 @ X20 @ (sk_D_4 @ X23 @ X20))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['12'])).
% 9.87/10.14  thf('53', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_4 @ X0 @ sk_B)))
% 9.87/10.14          | ~ (v1_funct_1 @ sk_B)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_B))),
% 9.87/10.14      inference('sup-', [status(thm)], ['51', '52'])).
% 9.87/10.14  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('56', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_4 @ X0 @ sk_B))))),
% 9.87/10.14      inference('demod', [status(thm)], ['53', '54', '55'])).
% 9.87/10.14  thf('57', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_C_1 @ X0 @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['50', '56'])).
% 9.87/10.14  thf('58', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_4) @ sk_A)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['48', '49'])).
% 9.87/10.14  thf('59', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('60', plain,
% 9.87/10.14      (![X20 : $i, X23 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X20))
% 9.87/10.14          | (r2_hidden @ (sk_D_4 @ X23 @ X20) @ (k1_relat_1 @ X20)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['18'])).
% 9.87/10.14  thf('61', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (sk_D_4 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 9.87/10.14          | ~ (v1_funct_1 @ sk_B)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_B))),
% 9.87/10.14      inference('sup-', [status(thm)], ['59', '60'])).
% 9.87/10.14  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('64', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (sk_D_4 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 9.87/10.14      inference('demod', [status(thm)], ['61', '62', '63'])).
% 9.87/10.14  thf('65', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B) @ 
% 9.87/10.14             (k1_relat_1 @ sk_B)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['58', '64'])).
% 9.87/10.14  thf('66', plain,
% 9.87/10.14      (![X20 : $i, X25 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['8'])).
% 9.87/10.14  thf('67', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14             (k2_relat_1 @ sk_B))
% 9.87/10.14          | ~ (v1_funct_1 @ sk_B)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_B))),
% 9.87/10.14      inference('sup-', [status(thm)], ['65', '66'])).
% 9.87/10.14  thf('68', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('71', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14             sk_A))),
% 9.87/10.14      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 9.87/10.14  thf('72', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('73', plain,
% 9.87/10.14      (![X14 : $i, X16 : $i]:
% 9.87/10.14         ((r2_hidden @ (k4_tarski @ X16 @ (sk_D_2 @ X16 @ X14)) @ X14)
% 9.87/10.14          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['22'])).
% 9.87/10.14  thf('74', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ X0 @ sk_C_4)) @ sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['72', '73'])).
% 9.87/10.14  thf('75', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ 
% 9.87/10.14              (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14              (sk_D_2 @ 
% 9.87/10.14               (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14               sk_C_4)) @ 
% 9.87/10.14             sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['71', '74'])).
% 9.87/10.14  thf('76', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('77', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_C_4)
% 9.87/10.14          | ((sk_D_2 @ 
% 9.87/10.14              (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14              sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['75', '76'])).
% 9.87/10.14  thf('78', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('79', plain, ((v1_funct_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('80', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ 
% 9.87/10.14              (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14              sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))))),
% 9.87/10.14      inference('demod', [status(thm)], ['77', '78', '79'])).
% 9.87/10.14  thf('81', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14            = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14               (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['57', '80'])).
% 9.87/10.14  thf('82', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['81'])).
% 9.87/10.14  thf('83', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14             sk_A))),
% 9.87/10.14      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 9.87/10.14  thf('84', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('85', plain,
% 9.87/10.14      (![X20 : $i, X25 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['8'])).
% 9.87/10.14  thf('86', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ sk_C_4 @ X0) @ (k2_relat_1 @ sk_C_4))
% 9.87/10.14          | ~ (v1_funct_1 @ sk_C_4)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['84', '85'])).
% 9.87/10.14  thf('87', plain, ((v1_funct_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('88', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('89', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k1_funct_1 @ sk_C_4 @ X0) @ (k2_relat_1 @ sk_C_4)))),
% 9.87/10.14      inference('demod', [status(thm)], ['86', '87', '88'])).
% 9.87/10.14  thf('90', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14              (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))) @ 
% 9.87/10.14             (k2_relat_1 @ sk_C_4)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['83', '89'])).
% 9.87/10.14  thf('91', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4) @ 
% 9.87/10.14           (k2_relat_1 @ sk_C_4))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['82', '90'])).
% 9.87/10.14  thf('92', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4) @ 
% 9.87/10.14             (k2_relat_1 @ sk_C_4)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['91'])).
% 9.87/10.14  thf('93', plain,
% 9.87/10.14      (![X20 : $i, X23 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X20)
% 9.87/10.14          | ~ (v1_funct_1 @ X20)
% 9.87/10.14          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X20))
% 9.87/10.14          | ((X23) = (k1_funct_1 @ X20 @ (sk_D_4 @ X23 @ X20))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['12'])).
% 9.87/10.14  thf('94', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14                 (sk_D_4 @ (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4) @ sk_C_4)))
% 9.87/10.14          | ~ (v1_funct_1 @ sk_C_4)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['92', '93'])).
% 9.87/10.14  thf('95', plain, ((v1_funct_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('96', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('97', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14                 (sk_D_4 @ (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4) @ sk_C_4))))),
% 9.87/10.14      inference('demod', [status(thm)], ['94', '95', '96'])).
% 9.87/10.14  thf('98', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14            = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14               (sk_D_4 @ (k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_C_4)) @ 
% 9.87/10.14                sk_C_4)))
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_C_4)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['45', '97'])).
% 9.87/10.14  thf('99', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('100', plain, ((v1_funct_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('101', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14            = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14               (sk_D_4 @ (k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_C_4)) @ 
% 9.87/10.14                sk_C_4)))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['98', '99', '100'])).
% 9.87/10.14  thf('102', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14                 (sk_D_4 @ (k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_C_4)) @ 
% 9.87/10.14                  sk_C_4))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['101'])).
% 9.87/10.14  thf('103', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4) = (sk_D @ X0 @ sk_C_4))
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_C_4)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['39', '102'])).
% 9.87/10.14  thf('104', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('105', plain, ((v1_funct_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('106', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4) = (sk_D @ X0 @ sk_C_4))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['103', '104', '105'])).
% 9.87/10.14  thf('107', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4) = (sk_D @ X0 @ sk_C_4)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['106'])).
% 9.87/10.14  thf('108', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_4) @ sk_A)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['48', '49'])).
% 9.87/10.14  thf('109', plain, (((k1_relat_1 @ sk_D_5) = (sk_A))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('110', plain,
% 9.87/10.14      (![X14 : $i, X16 : $i]:
% 9.87/10.14         ((r2_hidden @ (k4_tarski @ X16 @ (sk_D_2 @ X16 @ X14)) @ X14)
% 9.87/10.14          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['22'])).
% 9.87/10.14  thf('111', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ X0 @ sk_D_5)) @ sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['109', '110'])).
% 9.87/10.14  thf('112', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_4) @ 
% 9.87/10.14              (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)) @ 
% 9.87/10.14             sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['108', '111'])).
% 9.87/10.14  thf('113', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('114', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_D_5)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_D_5)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14              = (k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_C_4))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['112', '113'])).
% 9.87/10.14  thf('115', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('116', plain, ((v1_funct_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('117', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14              = (k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_C_4))))),
% 9.87/10.14      inference('demod', [status(thm)], ['114', '115', '116'])).
% 9.87/10.14  thf('118', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B) @ 
% 9.87/10.14             (k1_relat_1 @ sk_B)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['58', '64'])).
% 9.87/10.14  thf(t23_funct_1, axiom,
% 9.87/10.14    (![A:$i,B:$i]:
% 9.87/10.14     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.87/10.14       ( ![C:$i]:
% 9.87/10.14         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.87/10.14           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 9.87/10.14             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 9.87/10.14               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 9.87/10.14  thf('119', plain,
% 9.87/10.14      (![X26 : $i, X27 : $i, X28 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X26)
% 9.87/10.14          | ~ (v1_funct_1 @ X26)
% 9.87/10.14          | ((k1_funct_1 @ (k5_relat_1 @ X27 @ X26) @ X28)
% 9.87/10.14              = (k1_funct_1 @ X26 @ (k1_funct_1 @ X27 @ X28)))
% 9.87/10.14          | ~ (r2_hidden @ X28 @ (k1_relat_1 @ X27))
% 9.87/10.14          | ~ (v1_funct_1 @ X27)
% 9.87/10.14          | ~ (v1_relat_1 @ X27))),
% 9.87/10.14      inference('cnf', [status(esa)], [t23_funct_1])).
% 9.87/10.14  thf('120', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_B)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_B)
% 9.87/10.14          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X1) @ 
% 9.87/10.14              (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))
% 9.87/10.14              = (k1_funct_1 @ X1 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))
% 9.87/10.14          | ~ (v1_funct_1 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X1))),
% 9.87/10.14      inference('sup-', [status(thm)], ['118', '119'])).
% 9.87/10.14  thf('121', plain, ((v1_relat_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('122', plain, ((v1_funct_1 @ sk_B)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('123', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X1) @ 
% 9.87/10.14              (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))
% 9.87/10.14              = (k1_funct_1 @ X1 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))
% 9.87/10.14          | ~ (v1_funct_1 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X1))),
% 9.87/10.14      inference('demod', [status(thm)], ['120', '121', '122'])).
% 9.87/10.14  thf('124', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_C_4 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['81'])).
% 9.87/10.14  thf('125', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14            = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_4) @ 
% 9.87/10.14               (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_C_4)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['123', '124'])).
% 9.87/10.14  thf('126', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('127', plain, ((v1_funct_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('128', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14            = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_4) @ 
% 9.87/10.14               (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['125', '126', '127'])).
% 9.87/10.14  thf('129', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_4) @ 
% 9.87/10.14                 (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['128'])).
% 9.87/10.14  thf('130', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X1) @ 
% 9.87/10.14              (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))
% 9.87/10.14              = (k1_funct_1 @ X1 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))
% 9.87/10.14          | ~ (v1_funct_1 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X1))),
% 9.87/10.14      inference('demod', [status(thm)], ['120', '121', '122'])).
% 9.87/10.14  thf('131', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_C_1 @ X0 @ sk_C_4)
% 9.87/10.14              = (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['50', '56'])).
% 9.87/10.14  thf('132', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14             sk_A))),
% 9.87/10.14      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 9.87/10.14  thf('133', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ X0 @ sk_D_5)) @ sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['109', '110'])).
% 9.87/10.14  thf('134', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ 
% 9.87/10.14              (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14              (sk_D_2 @ 
% 9.87/10.14               (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14               sk_D_5)) @ 
% 9.87/10.14             sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['132', '133'])).
% 9.87/10.14  thf('135', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('136', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_D_5)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_D_5)
% 9.87/10.14          | ((sk_D_2 @ 
% 9.87/10.14              (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14              sk_D_5)
% 9.87/10.14              = (k1_funct_1 @ sk_D_5 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['134', '135'])).
% 9.87/10.14  thf('137', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('138', plain, ((v1_funct_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('139', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ 
% 9.87/10.14              (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)) @ 
% 9.87/10.14              sk_D_5)
% 9.87/10.14              = (k1_funct_1 @ sk_D_5 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))))),
% 9.87/10.14      inference('demod', [status(thm)], ['136', '137', '138'])).
% 9.87/10.14  thf('140', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14            = (k1_funct_1 @ sk_D_5 @ 
% 9.87/10.14               (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['131', '139'])).
% 9.87/10.14  thf('141', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14              = (k1_funct_1 @ sk_D_5 @ 
% 9.87/10.14                 (k1_funct_1 @ sk_B @ (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['140'])).
% 9.87/10.14  thf('142', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14            = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_D_5) @ 
% 9.87/10.14               (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))
% 9.87/10.14          | ~ (v1_relat_1 @ sk_D_5)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_D_5)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['130', '141'])).
% 9.87/10.14  thf('143', plain,
% 9.87/10.14      (((k5_relat_1 @ sk_B @ sk_C_4) = (k5_relat_1 @ sk_B @ sk_D_5))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('144', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('145', plain, ((v1_funct_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('146', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14            = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_4) @ 
% 9.87/10.14               (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B)))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 9.87/10.14  thf('147', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14              = (k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_4) @ 
% 9.87/10.14                 (sk_D_4 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_B))))),
% 9.87/10.14      inference('simplify', [status(thm)], ['146'])).
% 9.87/10.14  thf('148', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14            = (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['129', '147'])).
% 9.87/10.14  thf('149', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_D_5)
% 9.87/10.14              = (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['148'])).
% 9.87/10.14  thf('150', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_C_4))
% 9.87/10.14            = (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['117', '149'])).
% 9.87/10.14  thf('151', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_C_4))
% 9.87/10.14              = (sk_D_2 @ (sk_C_1 @ X0 @ sk_C_4) @ sk_C_4)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['150'])).
% 9.87/10.14  thf('152', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_C_4))
% 9.87/10.14            = (sk_D @ X0 @ sk_C_4))
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['107', '151'])).
% 9.87/10.14  thf('153', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | ((k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_C_4))
% 9.87/10.14              = (sk_D @ X0 @ sk_C_4)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['152'])).
% 9.87/10.14  thf('154', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_4) @ sk_A)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['48', '49'])).
% 9.87/10.14  thf('155', plain, (((k1_relat_1 @ sk_D_5) = (sk_A))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('156', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 9.87/10.14          | ((X31) != (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('157', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X30)
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X29 @ (k1_funct_1 @ X30 @ X29)) @ X30)
% 9.87/10.14          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X30)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['156'])).
% 9.87/10.14  thf('158', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_5 @ X0)) @ sk_D_5)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_D_5)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['155', '157'])).
% 9.87/10.14  thf('159', plain, ((v1_funct_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('160', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('161', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_5 @ X0)) @ sk_D_5))),
% 9.87/10.14      inference('demod', [status(thm)], ['158', '159', '160'])).
% 9.87/10.14  thf('162', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_4) @ 
% 9.87/10.14              (k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_C_4))) @ 
% 9.87/10.14             sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['154', '161'])).
% 9.87/10.14  thf('163', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ 
% 9.87/10.14           (k4_tarski @ (sk_C_1 @ X0 @ sk_C_4) @ (sk_D @ X0 @ sk_C_4)) @ sk_D_5)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_C_4 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['153', '162'])).
% 9.87/10.14  thf('164', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_C_4 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_4) @ (sk_D @ X0 @ sk_C_4)) @ 
% 9.87/10.14             sk_D_5))),
% 9.87/10.14      inference('simplify', [status(thm)], ['163'])).
% 9.87/10.14  thf('165', plain,
% 9.87/10.14      (![X7 : $i, X8 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ 
% 9.87/10.14             X7)
% 9.87/10.14          | (r1_tarski @ X8 @ X7)
% 9.87/10.14          | ~ (v1_relat_1 @ X8))),
% 9.87/10.14      inference('cnf', [status(esa)], [d3_relat_1])).
% 9.87/10.14  thf('166', plain,
% 9.87/10.14      (((r1_tarski @ sk_C_4 @ sk_D_5)
% 9.87/10.14        | ~ (v1_relat_1 @ sk_C_4)
% 9.87/10.14        | (r1_tarski @ sk_C_4 @ sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['164', '165'])).
% 9.87/10.14  thf('167', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('168', plain,
% 9.87/10.14      (((r1_tarski @ sk_C_4 @ sk_D_5) | (r1_tarski @ sk_C_4 @ sk_D_5))),
% 9.87/10.14      inference('demod', [status(thm)], ['166', '167'])).
% 9.87/10.14  thf('169', plain, ((r1_tarski @ sk_C_4 @ sk_D_5)),
% 9.87/10.14      inference('simplify', [status(thm)], ['168'])).
% 9.87/10.14  thf(d10_xboole_0, axiom,
% 9.87/10.14    (![A:$i,B:$i]:
% 9.87/10.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.87/10.14  thf('170', plain,
% 9.87/10.14      (![X4 : $i, X6 : $i]:
% 9.87/10.14         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 9.87/10.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.87/10.14  thf('171', plain,
% 9.87/10.14      ((~ (r1_tarski @ sk_D_5 @ sk_C_4) | ((sk_D_5) = (sk_C_4)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['169', '170'])).
% 9.87/10.14  thf('172', plain, (((sk_C_4) != (sk_D_5))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('173', plain, (~ (r1_tarski @ sk_D_5 @ sk_C_4)),
% 9.87/10.14      inference('simplify_reflect-', [status(thm)], ['171', '172'])).
% 9.87/10.14  thf('174', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 9.87/10.14          | ~ (v1_funct_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | ~ (v1_relat_1 @ X0))),
% 9.87/10.14      inference('simplify', [status(thm)], ['2'])).
% 9.87/10.14  thf('175', plain, (((k1_relat_1 @ sk_D_5) = (sk_A))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('176', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X0)
% 9.87/10.14          | (r1_tarski @ X0 @ X1)
% 9.87/10.14          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 9.87/10.14      inference('sup-', [status(thm)], ['4', '6'])).
% 9.87/10.14  thf('177', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_C_1 @ X0 @ sk_D_5) @ sk_A)
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_D_5))),
% 9.87/10.14      inference('sup+', [status(thm)], ['175', '176'])).
% 9.87/10.14  thf('178', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('179', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ (sk_C_1 @ X0 @ sk_D_5) @ sk_A)
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['177', '178'])).
% 9.87/10.14  thf('180', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('181', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i]:
% 9.87/10.14         (~ (v1_relat_1 @ X30)
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X29 @ (k1_funct_1 @ X30 @ X29)) @ X30)
% 9.87/10.14          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X30)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['156'])).
% 9.87/10.14  thf('182', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_4 @ X0)) @ sk_C_4)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_C_4)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['180', '181'])).
% 9.87/10.14  thf('183', plain, ((v1_funct_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('184', plain, ((v1_relat_1 @ sk_C_4)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('185', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ sk_A)
% 9.87/10.14          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_4 @ X0)) @ sk_C_4))),
% 9.87/10.14      inference('demod', [status(thm)], ['182', '183', '184'])).
% 9.87/10.14  thf('186', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X0 @ sk_D_5) @ 
% 9.87/10.14              (k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))) @ 
% 9.87/10.14             sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['179', '185'])).
% 9.87/10.14  thf('187', plain, ((r1_tarski @ sk_C_4 @ sk_D_5)),
% 9.87/10.14      inference('simplify', [status(thm)], ['168'])).
% 9.87/10.14  thf(d3_tarski, axiom,
% 9.87/10.14    (![A:$i,B:$i]:
% 9.87/10.14     ( ( r1_tarski @ A @ B ) <=>
% 9.87/10.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.87/10.14  thf('188', plain,
% 9.87/10.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.87/10.14         (~ (r2_hidden @ X0 @ X1)
% 9.87/10.14          | (r2_hidden @ X0 @ X2)
% 9.87/10.14          | ~ (r1_tarski @ X1 @ X2))),
% 9.87/10.14      inference('cnf', [status(esa)], [d3_tarski])).
% 9.87/10.14  thf('189', plain,
% 9.87/10.14      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_5) | ~ (r2_hidden @ X0 @ sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['187', '188'])).
% 9.87/10.14  thf('190', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X0 @ sk_D_5) @ 
% 9.87/10.14              (k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))) @ 
% 9.87/10.14             sk_D_5))),
% 9.87/10.14      inference('sup-', [status(thm)], ['186', '189'])).
% 9.87/10.14  thf('191', plain,
% 9.87/10.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 9.87/10.14          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 9.87/10.14          | ~ (v1_funct_1 @ X30)
% 9.87/10.14          | ~ (v1_relat_1 @ X30))),
% 9.87/10.14      inference('cnf', [status(esa)], [t8_funct_1])).
% 9.87/10.14  thf('192', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | ~ (v1_relat_1 @ sk_D_5)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_D_5)
% 9.87/10.14          | ((k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))
% 9.87/10.14              = (k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_D_5))))),
% 9.87/10.14      inference('sup-', [status(thm)], ['190', '191'])).
% 9.87/10.14  thf('193', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('194', plain, ((v1_funct_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('195', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | ((k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))
% 9.87/10.14              = (k1_funct_1 @ sk_D_5 @ (sk_C_1 @ X0 @ sk_D_5))))),
% 9.87/10.14      inference('demod', [status(thm)], ['192', '193', '194'])).
% 9.87/10.14  thf('196', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))
% 9.87/10.14            = (sk_D @ X0 @ sk_D_5))
% 9.87/10.14          | ~ (v1_relat_1 @ sk_D_5)
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | ~ (v1_funct_1 @ sk_D_5)
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['174', '195'])).
% 9.87/10.14  thf('197', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('198', plain, ((v1_funct_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('199', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         (((k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))
% 9.87/10.14            = (sk_D @ X0 @ sk_D_5))
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0))),
% 9.87/10.14      inference('demod', [status(thm)], ['196', '197', '198'])).
% 9.87/10.14  thf('200', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | ((k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))
% 9.87/10.14              = (sk_D @ X0 @ sk_D_5)))),
% 9.87/10.14      inference('simplify', [status(thm)], ['199'])).
% 9.87/10.14  thf('201', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X0 @ sk_D_5) @ 
% 9.87/10.14              (k1_funct_1 @ sk_C_4 @ (sk_C_1 @ X0 @ sk_D_5))) @ 
% 9.87/10.14             sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['179', '185'])).
% 9.87/10.14  thf('202', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r2_hidden @ 
% 9.87/10.14           (k4_tarski @ (sk_C_1 @ X0 @ sk_D_5) @ (sk_D @ X0 @ sk_D_5)) @ sk_C_4)
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | (r1_tarski @ sk_D_5 @ X0))),
% 9.87/10.14      inference('sup+', [status(thm)], ['200', '201'])).
% 9.87/10.14  thf('203', plain,
% 9.87/10.14      (![X0 : $i]:
% 9.87/10.14         ((r1_tarski @ sk_D_5 @ X0)
% 9.87/10.14          | (r2_hidden @ 
% 9.87/10.14             (k4_tarski @ (sk_C_1 @ X0 @ sk_D_5) @ (sk_D @ X0 @ sk_D_5)) @ 
% 9.87/10.14             sk_C_4))),
% 9.87/10.14      inference('simplify', [status(thm)], ['202'])).
% 9.87/10.14  thf('204', plain,
% 9.87/10.14      (![X7 : $i, X8 : $i]:
% 9.87/10.14         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ 
% 9.87/10.14             X7)
% 9.87/10.14          | (r1_tarski @ X8 @ X7)
% 9.87/10.14          | ~ (v1_relat_1 @ X8))),
% 9.87/10.14      inference('cnf', [status(esa)], [d3_relat_1])).
% 9.87/10.14  thf('205', plain,
% 9.87/10.14      (((r1_tarski @ sk_D_5 @ sk_C_4)
% 9.87/10.14        | ~ (v1_relat_1 @ sk_D_5)
% 9.87/10.14        | (r1_tarski @ sk_D_5 @ sk_C_4))),
% 9.87/10.14      inference('sup-', [status(thm)], ['203', '204'])).
% 9.87/10.14  thf('206', plain, ((v1_relat_1 @ sk_D_5)),
% 9.87/10.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.87/10.14  thf('207', plain,
% 9.87/10.14      (((r1_tarski @ sk_D_5 @ sk_C_4) | (r1_tarski @ sk_D_5 @ sk_C_4))),
% 9.87/10.14      inference('demod', [status(thm)], ['205', '206'])).
% 9.87/10.14  thf('208', plain, ((r1_tarski @ sk_D_5 @ sk_C_4)),
% 9.87/10.14      inference('simplify', [status(thm)], ['207'])).
% 9.87/10.14  thf('209', plain, ($false), inference('demod', [status(thm)], ['173', '208'])).
% 9.87/10.14  
% 9.87/10.14  % SZS output end Refutation
% 9.87/10.14  
% 9.87/10.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
