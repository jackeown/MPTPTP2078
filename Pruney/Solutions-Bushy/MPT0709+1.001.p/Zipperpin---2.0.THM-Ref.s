%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0709+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MQQBOZGLfc

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:22 EST 2020

% Result     : Theorem 50.52s
% Output     : Refutation 50.52s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 512 expanded)
%              Number of leaves         :   22 ( 158 expanded)
%              Depth                    :   25
%              Number of atoms          : 1778 (7488 expanded)
%              Number of equality atoms :   27 ( 210 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ X13 )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ ( sk_D_1 @ X13 @ X14 @ X15 ) ) @ X14 )
      | ( X13
        = ( k10_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ X13 )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( X13
        = ( k10_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( X16
       != ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X15 @ X18 ) @ X14 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X15 @ X18 ) @ X14 )
      | ( r2_hidden @ X18 @ ( k10_relat_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ X2 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ X2 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ ( k10_relat_1 @ X0 @ X3 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X2
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X2
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X0 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ X0 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('11',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ X3 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_funct_1 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_funct_1 @ X1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( r1_tarski @ ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X15 @ X18 ) @ X14 )
      | ( r2_hidden @ X18 @ ( k10_relat_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ ( k10_relat_1 @ sk_B @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) ) @ X2 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ ( k10_relat_1 @ sk_B @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ~ ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k10_relat_1 @ X2 @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57','58'])).

thf('60',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ~ ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['68'])).

thf('70',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('73',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X15 @ ( sk_D_1 @ X13 @ X14 @ X15 ) ) @ X14 )
      | ( X13
        = ( k10_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('79',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) @ X1 @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('97',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X15 @ X18 ) @ X14 )
      | ( r2_hidden @ X18 @ ( k10_relat_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) @ X1 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_A ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X22 )
      | ~ ( r2_hidden @ ( sk_C @ X22 @ X20 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','108'])).

thf('110',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X17 ) @ X14 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('111',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X17 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('114',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('115',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['81','115'])).


%------------------------------------------------------------------------------
