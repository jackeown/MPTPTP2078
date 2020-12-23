%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sJoDz5JMNi

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 158 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   21
%              Number of atoms          : 1100 (2225 expanded)
%              Number of equality atoms :   63 ( 134 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t56_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( ( k7_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('9',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

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

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ( X29
       != ( k2_funct_1 @ X28 ) )
      | ( ( k1_relat_1 @ X29 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('11',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X28 ) )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v2_funct_1 @ X28 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

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

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) @ X8 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X6 @ X8 ) ) )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_2 @ X19 @ X21 @ X22 )
      | ( X21
       != ( k1_funct_1 @ X22 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('36',plain,(
    ! [X19: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X22 ) )
      | ( zip_tseitin_2 @ X19 @ ( k1_funct_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ( X29
       != ( k2_funct_1 @ X28 ) )
      | ( zip_tseitin_3 @ X32 @ X31 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('41',plain,(
    ! [X28: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( zip_tseitin_3 @ X32 @ X31 @ ( k2_funct_1 @ X28 ) @ X28 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v2_funct_1 @ X28 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_2 @ X23 @ X24 @ X25 )
      | ( X23
        = ( k1_funct_1 @ X26 @ X24 ) )
      | ~ ( zip_tseitin_3 @ X23 @ X24 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['33','52'])).

thf('54',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('57',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('58',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('61',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','61'])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sJoDz5JMNi
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:02:12 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 65 iterations in 0.042s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(t56_funct_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.48         ( ( ( A ) =
% 0.21/0.48             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.48           ( ( A ) =
% 0.21/0.48             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.48            ( ( ( A ) =
% 0.21/0.48                ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.48              ( ( A ) =
% 0.21/0.48                ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t56_funct_1])).
% 0.21/0.48  thf('0', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k2_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.48         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf(t98_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X2 : $i]:
% 0.21/0.48         (((k7_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.21/0.48  thf(t99_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( r1_tarski @
% 0.21/0.48         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) @ 
% 0.21/0.48           (k2_relat_1 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t99_relat_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf(t54_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ A ) =>
% 0.21/0.48         ( ![B:$i]:
% 0.21/0.48           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.48             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.48               ( ( ![C:$i,D:$i]:
% 0.21/0.48                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.48                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.21/0.48                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.48                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.21/0.48                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.48                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.48                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.48                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.21/0.48                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.21/0.48       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.21/0.48         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.48           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_4, axiom,
% 0.21/0.48    (![D:$i,C:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.21/0.48       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.48         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_6, axiom,
% 0.21/0.48    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.21/0.48       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.48         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.48           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_8, axiom,
% 0.21/0.48    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.48       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.48         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_9, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ A ) =>
% 0.21/0.48         ( ![B:$i]:
% 0.21/0.48           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.48               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.21/0.48                 ( ![C:$i,D:$i]:
% 0.21/0.48                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.21/0.48                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X28 : $i, X29 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X28)
% 0.21/0.48          | ~ (v1_relat_1 @ X29)
% 0.21/0.48          | ~ (v1_funct_1 @ X29)
% 0.21/0.48          | ((X29) != (k2_funct_1 @ X28))
% 0.21/0.48          | ((k1_relat_1 @ X29) = (k2_relat_1 @ X28))
% 0.21/0.48          | ~ (v1_funct_1 @ X28)
% 0.21/0.48          | ~ (v1_relat_1 @ X28))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X28 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X28)
% 0.21/0.48          | ~ (v1_funct_1 @ X28)
% 0.21/0.48          | ((k1_relat_1 @ (k2_funct_1 @ X28)) = (k2_relat_1 @ X28))
% 0.21/0.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X28))
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X28))
% 0.21/0.48          | ~ (v2_funct_1 @ X28))),
% 0.21/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf(t46_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.48             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) = (k1_relat_1 @ X1))
% 0.21/0.48          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)))
% 0.21/0.48              = (k1_relat_1 @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.48              = (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.48              = (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.48              = (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X0)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.48              = (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf(t22_funct_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.48             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.21/0.48               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X6)
% 0.21/0.48          | ~ (v1_funct_1 @ X6)
% 0.21/0.48          | ((k1_funct_1 @ (k5_relat_1 @ X6 @ X7) @ X8)
% 0.21/0.48              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X6 @ X8)))
% 0.21/0.48          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X7)))
% 0.21/0.48          | ~ (v1_funct_1 @ X7)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 0.21/0.48              = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 0.21/0.48            = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.21/0.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 0.21/0.48              = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 0.21/0.48            = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 0.21/0.48              = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 0.21/0.48            = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.48        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.48        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.48            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '28'])).
% 0.21/0.48  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.48         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.48  thf('34', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.21/0.48         ((zip_tseitin_2 @ X19 @ X21 @ X22)
% 0.21/0.48          | ((X21) != (k1_funct_1 @ X22 @ X19))
% 0.21/0.48          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X22)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X19 : $i, X22 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X22))
% 0.21/0.48          | (zip_tseitin_2 @ X19 @ (k1_funct_1 @ X22 @ X19) @ X22))),
% 0.21/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X28)
% 0.21/0.48          | ~ (v1_relat_1 @ X29)
% 0.21/0.48          | ~ (v1_funct_1 @ X29)
% 0.21/0.48          | ((X29) != (k2_funct_1 @ X28))
% 0.21/0.48          | (zip_tseitin_3 @ X32 @ X31 @ X29 @ X28)
% 0.21/0.48          | ~ (v1_funct_1 @ X28)
% 0.21/0.48          | ~ (v1_relat_1 @ X28))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X28 : $i, X31 : $i, X32 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X28)
% 0.21/0.48          | ~ (v1_funct_1 @ X28)
% 0.21/0.48          | (zip_tseitin_3 @ X32 @ X31 @ (k2_funct_1 @ X28) @ X28)
% 0.21/0.48          | ~ (v1_funct_1 @ (k2_funct_1 @ X28))
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X28))
% 0.21/0.48          | ~ (v2_funct_1 @ X28))),
% 0.21/0.48      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         (~ (zip_tseitin_2 @ X23 @ X24 @ X25)
% 0.21/0.48          | ((X23) = (k1_funct_1 @ X26 @ X24))
% 0.21/0.48          | ~ (zip_tseitin_3 @ X23 @ X24 @ X26 @ X25))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.21/0.48          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      ((((sk_A)
% 0.21/0.48          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.48        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '47'])).
% 0.21/0.48  thf('49', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (((sk_A)
% 0.21/0.48         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.48         = (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '52'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      ((((sk_A)
% 0.21/0.48          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.48        | ((sk_A)
% 0.21/0.48            != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((((sk_A)
% 0.21/0.48          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((sk_A)
% 0.21/0.48                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.48                   sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (((sk_A)
% 0.21/0.48         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      ((((sk_A)
% 0.21/0.48          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((sk_A)
% 0.21/0.48                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.48                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.21/0.48      inference('split', [status(esa)], ['54'])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((((sk_A) != (sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((sk_A)
% 0.21/0.48                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.48                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      ((((sk_A)
% 0.21/0.48          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((sk_A)
% 0.21/0.48          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))) | 
% 0.21/0.48       ~
% 0.21/0.48       (((sk_A)
% 0.21/0.48          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['54'])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((sk_A)
% 0.21/0.48          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      (((sk_A)
% 0.21/0.48         != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['55', '61'])).
% 0.21/0.48  thf('63', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['53', '62'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
