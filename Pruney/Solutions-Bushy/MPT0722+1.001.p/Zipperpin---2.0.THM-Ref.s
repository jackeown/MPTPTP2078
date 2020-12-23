%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0722+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XtR0C1Yjoq

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:23 EST 2020

% Result     : Theorem 16.15s
% Output     : Refutation 16.15s
% Verified   : 
% Statistics : Number of formulae       :  221 (1237 expanded)
%              Number of leaves         :   40 ( 373 expanded)
%              Depth                    :   54
%              Number of atoms          : 2726 (17383 expanded)
%              Number of equality atoms :   70 ( 577 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

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

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('10',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t177_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v2_funct_1 @ A )
              & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
           => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t177_funct_1])).

thf('12',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t54_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ! [C: $i,D: $i] :
                    ( ( ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) )
                     => ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) )
                    & ( ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) )
                     => ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) )
                & ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_3 @ X30 @ X32 @ X33 )
      | ( X32
       != ( k1_funct_1 @ X33 @ X30 ) )
      | ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('17',plain,(
    ! [X30: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X33 ) )
      | ( zip_tseitin_3 @ X30 @ ( k1_funct_1 @ X33 @ X30 ) @ X33 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_3 @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(zf_stmt_5,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_4 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_3 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_1 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) )
                & ! [C: $i,D: $i] :
                    ( ( zip_tseitin_4 @ D @ C @ B @ A )
                    & ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i,X42: $i,X43: $i] :
      ( ~ ( v2_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_funct_1 @ X40 )
      | ( X40
       != ( k2_funct_1 @ X39 ) )
      | ( zip_tseitin_4 @ X43 @ X42 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('22',plain,(
    ! [X39: $i,X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_funct_1 @ X39 )
      | ( zip_tseitin_4 @ X43 @ X42 @ ( k2_funct_1 @ X39 ) @ X39 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X39 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X39 ) )
      | ~ ( v2_funct_1 @ X39 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_4 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_4 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_4 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_4 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_3 @ X34 @ X35 @ X36 )
      | ( X34
        = ( k1_funct_1 @ X37 @ X35 ) )
      | ~ ( zip_tseitin_4 @ X34 @ X35 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X19 @ X18 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X44: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relat_1 @ X44 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ X2 @ ( k2_funct_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) @ X1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) @ X1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['9','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('72',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,
    ( ( r1_tarski @ sk_B @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_B @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ sk_B @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X1 @ X0 ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','78'])).

thf('80',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
    | ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['79'])).

thf('81',plain,(
    ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('82',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('85',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('89',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    r2_hidden @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('92',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('104',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('107',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('115',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('118',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('122',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('125',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('127',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('128',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('130',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('133',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X30: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X33 ) )
      | ( zip_tseitin_3 @ X30 @ ( k1_funct_1 @ X33 @ X30 ) @ X33 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('135',plain,(
    zip_tseitin_3 @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('138',plain,
    ( ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    zip_tseitin_3 @ ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('141',plain,
    ( ( ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('144',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('145',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( ( sk_D @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_E @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_D @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_E @ X0 @ X2 @ X1 ) ) )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ( ( sk_D @ X0 @ X2 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_E @ X0 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) )
    | ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','150'])).

thf('152',plain,(
    ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('153',plain,
    ( ( ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['143','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('156',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('160',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('161',plain,
    ( ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('163',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('164',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('165',plain,
    ( ( sk_E_1 @ ( sk_E @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B @ sk_A )
    = ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','161','162','163','164'])).

thf('166',plain,(
    r2_hidden @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['130','165'])).

thf('167',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('173',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('177',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('178',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ sk_B ) @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    $false ),
    inference('sup-',[status(thm)],['101','178'])).


%------------------------------------------------------------------------------
