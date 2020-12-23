%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZmVYCEPrHC

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 961 expanded)
%              Number of leaves         :   28 ( 287 expanded)
%              Depth                    :   25
%              Number of atoms          : 1401 (23423 expanded)
%              Number of equality atoms :   90 (2262 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t60_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k1_relat_1 @ A )
                = ( k2_relat_1 @ B ) )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i,D: $i] :
                  ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                 => ( ( ( k1_funct_1 @ A @ C )
                      = D )
                  <=> ( ( k1_funct_1 @ B @ D )
                      = C ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k1_relat_1 @ A )
                  = ( k2_relat_1 @ B ) )
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [C: $i,D: $i] :
                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                      & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                   => ( ( ( k1_funct_1 @ A @ C )
                        = D )
                    <=> ( ( k1_funct_1 @ B @ D )
                        = C ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_1])).

thf('0',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X7 @ X8 @ X9 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_3 @ X16 @ X17 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X16 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(zf_stmt_3,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_9,axiom,(
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
                    ( ( zip_tseitin_3 @ D @ C @ B @ A )
                    & ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
       != ( k2_relat_1 @ X21 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X22 @ X21 ) @ ( sk_C @ X22 @ X21 ) @ X22 @ X21 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X22 @ X21 ) @ ( sk_C @ X22 @ X21 ) @ X22 @ X21 )
      | ( X22
        = ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_2 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ ( sk_D @ sk_B @ X0 ) @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ sk_B @ X0 ) @ ( sk_C @ sk_B @ X0 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ ( sk_D @ sk_B @ X0 ) @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ sk_B @ X0 ) @ ( sk_C @ sk_B @ X0 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('11',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X4
        = ( k1_funct_1 @ X5 @ X2 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('18',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( zip_tseitin_2 @ X12 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( zip_tseitin_2 @ X12 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X27 )
        = X26 )
      | ( ( k1_funct_1 @ sk_A @ X26 )
       != X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X26: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ X26 ) )
        = X26 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X26 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X26: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ X26 ) )
        = X26 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X26 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X26 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k2_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ X26 ) )
        = X26 ) ) ),
    inference(clc,[status(thm)],['30','36'])).

thf('38',plain,
    ( ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) )
      = ( sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','37'])).

thf('39',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_D @ sk_B @ sk_A ) )
    | ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['20','38'])).

thf('40',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    = ( sk_D @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_relat_1 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('43',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( zip_tseitin_2 @ X12 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( zip_tseitin_2 @ X12 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_A @ X26 )
        = X27 )
      | ( ( k1_funct_1 @ sk_B @ X27 )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X27: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X27 ) )
        = X27 )
      | ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X27 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X27: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X27 ) )
        = X27 )
      | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X27 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X27 ) )
        = X27 ) ) ),
    inference(clc,[status(thm)],['57','63'])).

thf('65',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) )
    | ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','64'])).

thf('66',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    = ( sk_D @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('67',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_3 @ X16 @ X17 @ X19 @ X20 )
      | ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X20 ) )
      | ( X16
       != ( k1_funct_1 @ X19 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('72',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X20 ) )
      | ( zip_tseitin_3 @ ( k1_funct_1 @ X19 @ X17 ) @ X17 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ ( k1_funct_1 @ X0 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    zip_tseitin_3 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['40','73'])).

thf('75',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
       != ( k2_relat_1 @ X21 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X22 @ X21 ) @ ( sk_C @ X22 @ X21 ) @ X22 @ X21 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X22 @ X21 ) @ ( sk_C @ X22 @ X21 ) @ X22 @ X21 )
      | ( X22
        = ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( zip_tseitin_1 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('81',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    = ( sk_D @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('83',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X7 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X11 ) )
      | ( X8
       != ( k1_funct_1 @ X11 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X11 ) )
      | ( zip_tseitin_1 @ X7 @ ( k1_funct_1 @ X11 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( zip_tseitin_1 @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_D @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( k1_funct_1 @ sk_A @ ( sk_D @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('90',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

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

thf('94',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','90','91','92','93','94'])).

thf('96',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZmVYCEPrHC
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 95 iterations in 0.055s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.51  thf(t60_funct_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51           ( ( ( v2_funct_1 @ A ) & 
% 0.20/0.51               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.20/0.51               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.51               ( ![C:$i,D:$i]:
% 0.20/0.51                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.51                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.20/0.51                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.20/0.51             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51              ( ( ( v2_funct_1 @ A ) & 
% 0.20/0.51                  ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.20/0.51                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.51                  ( ![C:$i,D:$i]:
% 0.20/0.51                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51                        ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.51                      ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.20/0.51                        ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.20/0.51                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t60_funct_1])).
% 0.20/0.51  thf('0', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t54_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.51       ( ( v2_funct_1 @ A ) =>
% 0.20/0.51         ( ![B:$i]:
% 0.20/0.51           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.51             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.51               ( ( ![C:$i,D:$i]:
% 0.20/0.51                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.51                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.20/0.51                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.51                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.20/0.51                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.51                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.51                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.51                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.20/0.51                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, axiom,
% 0.20/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.20/0.51       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.20/0.51         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.51         ((zip_tseitin_1 @ X7 @ X8 @ X9 @ X11)
% 0.20/0.51          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf(zf_stmt_2, axiom,
% 0.20/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.20/0.51       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.20/0.51         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.51           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((zip_tseitin_3 @ X16 @ X17 @ X19 @ X20)
% 0.20/0.51          | (zip_tseitin_2 @ X16 @ X17 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_5, axiom,
% 0.20/0.51    (![D:$i,C:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.20/0.51       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_6, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_8, axiom,
% 0.20/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.51       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.51         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_9, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ( v2_funct_1 @ A ) =>
% 0.20/0.51         ( ![B:$i]:
% 0.20/0.51           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.51               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.20/0.51                 ( ![C:$i,D:$i]:
% 0.20/0.51                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.20/0.51                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ X21)
% 0.20/0.51          | ~ (v1_relat_1 @ X22)
% 0.20/0.51          | ~ (v1_funct_1 @ X22)
% 0.20/0.51          | ((k1_relat_1 @ X22) != (k2_relat_1 @ X21))
% 0.20/0.51          | ~ (zip_tseitin_3 @ (sk_D @ X22 @ X21) @ (sk_C @ X22 @ X21) @ X22 @ 
% 0.20/0.51               X21)
% 0.20/0.51          | ~ (zip_tseitin_1 @ (sk_D @ X22 @ X21) @ (sk_C @ X22 @ X21) @ X22 @ 
% 0.20/0.51               X21)
% 0.20/0.51          | ((X22) = (k2_funct_1 @ X21))
% 0.20/0.51          | ~ (v1_funct_1 @ X21)
% 0.20/0.51          | ~ (v1_relat_1 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((zip_tseitin_2 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((X1) = (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (zip_tseitin_1 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v2_funct_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X1 @ X0)
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.20/0.51          | ((X1) = (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | (zip_tseitin_2 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 0.20/0.51          | (zip_tseitin_2 @ (sk_D @ sk_B @ X0) @ (sk_C @ sk_B @ X0) @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((sk_B) = (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | (zip_tseitin_0 @ (sk_D @ sk_B @ X0) @ (sk_C @ sk_B @ X0) @ sk_B @ 
% 0.20/0.51             X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.51  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 0.20/0.51          | (zip_tseitin_2 @ (sk_D @ sk_B @ X0) @ (sk_C @ sk_B @ X0) @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((sk_B) = (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | (zip_tseitin_0 @ (sk_D @ sk_B @ X0) @ (sk_C @ sk_B @ X0) @ sk_B @ 
% 0.20/0.51             X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((zip_tseitin_0 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_B @ 
% 0.20/0.51         sk_A)
% 0.20/0.51        | ~ (v2_funct_1 @ sk_A)
% 0.20/0.51        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.20/0.51        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.51        | (zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.51      inference('eq_res', [status(thm)], ['9'])).
% 0.20/0.51  thf('11', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((zip_tseitin_0 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_B @ 
% 0.20/0.51         sk_A)
% 0.20/0.51        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.20/0.51        | (zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.20/0.51  thf('15', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((zip_tseitin_0 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_B @ 
% 0.20/0.51         sk_A)
% 0.20/0.51        | (zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (((X4) = (k1_funct_1 @ X5 @ X2))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X4 @ X2 @ X5 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.51        | ((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X14) = (k1_funct_1 @ X13 @ X12))
% 0.20/0.51          | ~ (zip_tseitin_2 @ X12 @ X14 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.51        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.51        | ((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         ((r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.20/0.51          | ~ (zip_tseitin_2 @ X12 @ X14 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.51        | (r2_hidden @ (sk_D @ sk_B @ sk_A) @ (k1_relat_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.51        | (r2_hidden @ (sk_D @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X26 @ (k1_relat_1 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X27 @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | ((k1_funct_1 @ sk_B @ X27) = (X26))
% 0.20/0.51          | ((k1_funct_1 @ sk_A @ X26) != (X27)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X26 : $i]:
% 0.20/0.51         (((k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_A @ X26)) = (X26))
% 0.20/0.51          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ X26) @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.51  thf('28', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X26 : $i]:
% 0.20/0.51         (((k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_A @ X26)) = (X26))
% 0.20/0.51          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ X26) @ (k2_relat_1 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X26 @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.51  thf('31', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t12_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.51         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.51          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X26 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X26 @ (k2_relat_1 @ sk_B))
% 0.20/0.51          | ((k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_A @ X26)) = (X26)))),
% 0.20/0.51      inference('clc', [status(thm)], ['30', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.51        | ((k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)))
% 0.20/0.51            = (sk_D @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) = (sk_D @ sk_B @ sk_A))
% 0.20/0.51        | ((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.51        | ((sk_D @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['20', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) = (sk_D @ sk_B @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((zip_tseitin_0 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_B @ 
% 0.20/0.51         sk_A)
% 0.20/0.51        | (zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         ((r2_hidden @ X2 @ (k2_relat_1 @ X3))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X4 @ X2 @ X5 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.51        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         ((r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.20/0.51          | ~ (zip_tseitin_2 @ X12 @ X14 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ (sk_D @ sk_B @ sk_A) @ (k1_relat_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ (sk_D @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)) @ 
% 0.20/0.51           (k2_relat_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (((zip_tseitin_2 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.51        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X14) = (k1_funct_1 @ X13 @ X12))
% 0.20/0.51          | ~ (zip_tseitin_2 @ X12 @ X14 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.51        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X26 @ (k1_relat_1 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X27 @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | ((k1_funct_1 @ sk_A @ X26) = (X27))
% 0.20/0.51          | ((k1_funct_1 @ sk_B @ X27) != (X26)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X27 : $i]:
% 0.20/0.51         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X27)) = (X27))
% 0.20/0.51          | ~ (r2_hidden @ X27 @ (k1_relat_1 @ sk_B))
% 0.20/0.51          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X27) @ (k1_relat_1 @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.51  thf('55', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X27 : $i]:
% 0.20/0.51         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X27)) = (X27))
% 0.20/0.51          | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X27) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.51  thf('58', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.20/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.52  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X27 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A))
% 0.20/0.52          | ((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X27)) = (X27)))),
% 0.20/0.52      inference('clc', [status(thm)], ['57', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)))
% 0.20/0.52        | ((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.52            = (sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['52', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) = (sk_D @ sk_B @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)))
% 0.20/0.52        | ((k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)) = (sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.20/0.52        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '68'])).
% 0.20/0.52  thf('70', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.20/0.52         ((zip_tseitin_3 @ X16 @ X17 @ X19 @ X20)
% 0.20/0.52          | ~ (r2_hidden @ X17 @ (k2_relat_1 @ X20))
% 0.20/0.52          | ((X16) != (k1_funct_1 @ X19 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X17 @ (k2_relat_1 @ X20))
% 0.20/0.52          | (zip_tseitin_3 @ (k1_funct_1 @ X19 @ X17) @ X17 @ X19 @ X20))),
% 0.20/0.52      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (zip_tseitin_3 @ (k1_funct_1 @ X0 @ (sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.52          (sk_C @ sk_B @ sk_A) @ X0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['70', '72'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((zip_tseitin_3 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ sk_B @ 
% 0.20/0.52        sk_A)),
% 0.20/0.52      inference('sup+', [status(thm)], ['40', '73'])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X21)
% 0.20/0.52          | ~ (v1_relat_1 @ X22)
% 0.20/0.52          | ~ (v1_funct_1 @ X22)
% 0.20/0.52          | ((k1_relat_1 @ X22) != (k2_relat_1 @ X21))
% 0.20/0.52          | ~ (zip_tseitin_3 @ (sk_D @ X22 @ X21) @ (sk_C @ X22 @ X21) @ X22 @ 
% 0.20/0.52               X21)
% 0.20/0.52          | ~ (zip_tseitin_1 @ (sk_D @ X22 @ X21) @ (sk_C @ X22 @ X21) @ X22 @ 
% 0.20/0.52               X21)
% 0.20/0.52          | ((X22) = (k2_funct_1 @ X21))
% 0.20/0.52          | ~ (v1_funct_1 @ X21)
% 0.20/0.52          | ~ (v1_relat_1 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.52        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.20/0.52        | ~ (zip_tseitin_1 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52             sk_B @ sk_A)
% 0.20/0.52        | ((k1_relat_1 @ sk_B) != (k2_relat_1 @ sk_A))
% 0.20/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('78', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('79', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.52        (k2_relat_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) = (sk_D @ sk_B @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.52  thf('83', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['81', '82'])).
% 0.20/0.52  thf('84', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.52         ((zip_tseitin_1 @ X7 @ X8 @ X9 @ X11)
% 0.20/0.52          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X11))
% 0.20/0.52          | ((X8) != (k1_funct_1 @ X11 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (![X7 : $i, X9 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X7 @ (k1_relat_1 @ X11))
% 0.20/0.52          | (zip_tseitin_1 @ X7 @ (k1_funct_1 @ X11 @ X7) @ X9 @ X11))),
% 0.20/0.52      inference('simplify', [status(thm)], ['85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.52          | (zip_tseitin_1 @ X0 @ (k1_funct_1 @ sk_A @ X0) @ X1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['84', '86'])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (zip_tseitin_1 @ (sk_D @ sk_B @ sk_A) @ 
% 0.20/0.52          (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)) @ X0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '87'])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_A @ (sk_D @ sk_B @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (zip_tseitin_1 @ (sk_D @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A) @ X0 @ 
% 0.20/0.52          sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.52  thf('91', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('93', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('94', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      ((((sk_B) = (k2_funct_1 @ sk_A))
% 0.20/0.52        | ((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['76', '77', '78', '90', '91', '92', '93', '94'])).
% 0.20/0.52  thf('96', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['95'])).
% 0.20/0.52  thf('97', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('98', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
