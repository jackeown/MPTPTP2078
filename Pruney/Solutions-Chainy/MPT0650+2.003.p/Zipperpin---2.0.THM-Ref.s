%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cxEFNMXqEr

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 194 expanded)
%              Number of leaves         :   33 (  70 expanded)
%              Depth                    :   21
%              Number of atoms          : 1118 (2745 expanded)
%              Number of equality atoms :   60 ( 171 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf(zf_stmt_0,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_8,axiom,(
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

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( X30
       != ( k2_funct_1 @ X29 ) )
      | ( zip_tseitin_1 @ X31 @ X32 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('3',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ( zip_tseitin_1 @ X31 @ X32 @ ( k2_funct_1 @ X29 ) @ X29 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v2_funct_1 @ X29 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_9,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('9',plain,(
    ! [X10: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 )
      | ( X12
       != ( k1_funct_1 @ X13 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('10',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X14 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X13 @ X10 ) @ X10 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( X16
        = ( k1_funct_1 @ X18 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B )
      | ( sk_A
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('17',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('18',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k2_relat_1 @ X34 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('23',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_2 @ X20 @ X22 @ X23 )
      | ( X22
       != ( k1_funct_1 @ X23 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X23 ) )
      | ( zip_tseitin_2 @ X20 @ ( k1_funct_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('30',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k1_relat_1 @ X34 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X23 ) )
      | ( zip_tseitin_2 @ X20 @ ( k1_funct_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ X1 ) @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('51',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) @ X9 )
        = ( k1_funct_1 @ X8 @ ( k1_funct_1 @ X7 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('58',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('66',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('68',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','69'])).

thf('71',plain,
    ( $false
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('74',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('77',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['71','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cxEFNMXqEr
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 97 iterations in 0.080s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(dt_k2_funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X6 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.21/0.54          | ~ (v1_funct_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X6 : $i]:
% 0.21/0.54         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.21/0.54          | ~ (v1_funct_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf(t54_funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.54       ( ( v2_funct_1 @ A ) =>
% 0.21/0.54         ( ![B:$i]:
% 0.21/0.54           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.54             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.54               ( ( ![C:$i,D:$i]:
% 0.21/0.54                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.54                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.21/0.54                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.54                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.21/0.54                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.54                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.54                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.54                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.21/0.54                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_1, axiom,
% 0.21/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.21/0.54       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.21/0.54         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.54           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_3, axiom,
% 0.21/0.54    (![D:$i,C:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.21/0.54       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.54         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_5, axiom,
% 0.21/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.21/0.54       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.54         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.54           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_7, axiom,
% 0.21/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.54       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.54         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_8, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ( v2_funct_1 @ A ) =>
% 0.21/0.54         ( ![B:$i]:
% 0.21/0.54           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.54               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.21/0.54                 ( ![C:$i,D:$i]:
% 0.21/0.54                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.21/0.54                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (v2_funct_1 @ X29)
% 0.21/0.54          | ~ (v1_relat_1 @ X30)
% 0.21/0.54          | ~ (v1_funct_1 @ X30)
% 0.21/0.54          | ((X30) != (k2_funct_1 @ X29))
% 0.21/0.54          | (zip_tseitin_1 @ X31 @ X32 @ X30 @ X29)
% 0.21/0.54          | ~ (v1_funct_1 @ X29)
% 0.21/0.54          | ~ (v1_relat_1 @ X29))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X29)
% 0.21/0.54          | ~ (v1_funct_1 @ X29)
% 0.21/0.54          | (zip_tseitin_1 @ X31 @ X32 @ (k2_funct_1 @ X29) @ X29)
% 0.21/0.54          | ~ (v1_funct_1 @ (k2_funct_1 @ X29))
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X29))
% 0.21/0.54          | ~ (v2_funct_1 @ X29))),
% 0.21/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.54  thf(t57_funct_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.21/0.54         ( ( ( A ) =
% 0.21/0.54             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.21/0.54           ( ( A ) =
% 0.21/0.54             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_9, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.21/0.54            ( ( ( A ) =
% 0.21/0.54                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.21/0.54              ( ( A ) =
% 0.21/0.54                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.21/0.54  thf('8', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X12 @ X10 @ X13 @ X14)
% 0.21/0.54          | ((X12) != (k1_funct_1 @ X13 @ X10))
% 0.21/0.54          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X10 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X10 @ (k2_relat_1 @ X14))
% 0.21/0.54          | (zip_tseitin_0 @ (k1_funct_1 @ X13 @ X10) @ X10 @ X13 @ X14))),
% 0.21/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (zip_tseitin_0 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.21/0.54          | ((X16) = (k1_funct_1 @ X18 @ X15))
% 0.21/0.54          | ~ (zip_tseitin_1 @ X15 @ X16 @ X17 @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (zip_tseitin_1 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)
% 0.21/0.54          | ((sk_A) = (k1_funct_1 @ sk_B @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.54        | ((sk_A)
% 0.21/0.54            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '13'])).
% 0.21/0.54  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('17', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (((sk_A)
% 0.21/0.54         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X6 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.21/0.54          | ~ (v1_funct_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X6 : $i]:
% 0.21/0.54         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.21/0.54          | ~ (v1_funct_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('21', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf(t55_funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ( v2_funct_1 @ A ) =>
% 0.21/0.54         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.54           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X34 : $i]:
% 0.21/0.54         (~ (v2_funct_1 @ X34)
% 0.21/0.54          | ((k2_relat_1 @ X34) = (k1_relat_1 @ (k2_funct_1 @ X34)))
% 0.21/0.54          | ~ (v1_funct_1 @ X34)
% 0.21/0.54          | ~ (v1_relat_1 @ X34))),
% 0.21/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.21/0.54         ((zip_tseitin_2 @ X20 @ X22 @ X23)
% 0.21/0.54          | ((X22) != (k1_funct_1 @ X23 @ X20))
% 0.21/0.54          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X23)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X20 : $i, X23 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X23))
% 0.21/0.54          | (zip_tseitin_2 @ X20 @ (k1_funct_1 @ X23 @ X20) @ X23))),
% 0.21/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | (zip_tseitin_2 @ X1 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 0.21/0.54             (k2_funct_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.21/0.54         (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.54  thf('27', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.21/0.54        (k2_funct_1 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         ((r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.21/0.54          | ~ (zip_tseitin_2 @ X20 @ X22 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('32', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X6 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.21/0.54          | ~ (v1_funct_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf(d3_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X1 : $i, X3 : $i]:
% 0.21/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X1 : $i, X3 : $i]:
% 0.21/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.54      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X34 : $i]:
% 0.21/0.54         (~ (v2_funct_1 @ X34)
% 0.21/0.54          | ((k1_relat_1 @ X34) = (k2_relat_1 @ (k2_funct_1 @ X34)))
% 0.21/0.54          | ~ (v1_funct_1 @ X34)
% 0.21/0.54          | ~ (v1_relat_1 @ X34))),
% 0.21/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.54  thf(t46_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ B ) =>
% 0.21/0.54           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.54             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X4)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4)) = (k1_relat_1 @ X5))
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X5) @ (k1_relat_1 @ X4))
% 0.21/0.54          | ~ (v1_relat_1 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.21/0.54              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.21/0.54              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.21/0.54              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.21/0.54              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v2_funct_1 @ X0)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.21/0.54              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X20 : $i, X23 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X23))
% 0.21/0.54          | (zip_tseitin_2 @ X20 @ (k1_funct_1 @ X23 @ X20) @ X23))),
% 0.21/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | (zip_tseitin_2 @ X1 @ 
% 0.21/0.54             (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ X1) @ 
% 0.21/0.54             (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((zip_tseitin_2 @ sk_A @ 
% 0.21/0.54         (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A) @ 
% 0.21/0.54         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.21/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '46'])).
% 0.21/0.54  thf('48', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((zip_tseitin_2 @ sk_A @ 
% 0.21/0.54        (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A) @ 
% 0.21/0.54        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         ((r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.21/0.54          | ~ (zip_tseitin_2 @ X20 @ X22 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((r2_hidden @ sk_A @ 
% 0.21/0.54        (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf(t22_funct_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.54             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.21/0.54               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X7)
% 0.21/0.54          | ~ (v1_funct_1 @ X7)
% 0.21/0.54          | ((k1_funct_1 @ (k5_relat_1 @ X7 @ X8) @ X9)
% 0.21/0.54              = (k1_funct_1 @ X8 @ (k1_funct_1 @ X7 @ X9)))
% 0.21/0.54          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X8)))
% 0.21/0.54          | ~ (v1_funct_1 @ X8)
% 0.21/0.54          | ~ (v1_relat_1 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.21/0.54            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      ((((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.21/0.54          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.21/0.54            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '58'])).
% 0.21/0.54  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.21/0.54            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.21/0.54            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '62'])).
% 0.21/0.54  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.21/0.54         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.21/0.54        | ((sk_A)
% 0.21/0.54            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.54                   sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['67'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.54                   sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '68'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      ((((sk_A) != (sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.54                   sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '69'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (($false)
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.54                   sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (((sk_A)
% 0.21/0.54         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ sk_B @ 
% 0.21/0.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.54      inference('split', [status(esa)], ['67'])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      ((((sk_A) != (sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ sk_B @ 
% 0.21/0.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (~
% 0.21/0.54       (((sk_A)
% 0.21/0.54          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.21/0.54       ~
% 0.21/0.54       (((sk_A)
% 0.21/0.54          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['67'])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (~
% 0.21/0.54       (((sk_A)
% 0.21/0.54          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.21/0.54  thf('78', plain, ($false),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['71', '77'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
