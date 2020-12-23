%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5A7BZufMBJ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 168 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  952 (2379 expanded)
%              Number of equality atoms :   47 ( 143 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('2',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X31: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relat_1 @ X31 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

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
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_2 @ X17 @ X19 @ X20 )
      | ( X19
       != ( k1_funct_1 @ X20 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X17: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) )
      | ( zip_tseitin_2 @ X17 @ ( k1_funct_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ ( k1_funct_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) @ X2 ) @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) @ X6 )
        = ( k1_funct_1 @ X5 @ ( k1_funct_1 @ X4 @ X6 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X17: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) )
      | ( zip_tseitin_2 @ X17 @ ( k1_funct_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('26',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

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

thf('29',plain,(
    ! [X26: $i,X27: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( X27
       != ( k2_funct_1 @ X26 ) )
      | ( zip_tseitin_3 @ X30 @ X29 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('30',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( zip_tseitin_3 @ X30 @ X29 @ ( k2_funct_1 @ X26 ) @ X26 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X26 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_2 @ X21 @ X22 @ X23 )
      | ( X21
        = ( k1_funct_1 @ X24 @ X22 ) )
      | ~ ( zip_tseitin_3 @ X21 @ X22 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['23','41','42','43'])).

thf('45',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('48',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('49',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('52',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['46','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5A7BZufMBJ
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 120 iterations in 0.067s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.53  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(dt_k2_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.53         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X3 : $i]:
% 0.21/0.53         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.53          | ~ (v1_funct_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X3 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.53          | ~ (v1_funct_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf(t56_funct_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.53         ( ( ( A ) =
% 0.21/0.53             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.53           ( ( A ) =
% 0.21/0.53             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.53            ( ( ( A ) =
% 0.21/0.53                ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.53              ( ( A ) =
% 0.21/0.53                ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t56_funct_1])).
% 0.21/0.53  thf('2', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X3 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.53          | ~ (v1_funct_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf(t169_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.53  thf(t55_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ A ) =>
% 0.21/0.53         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.53           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X31 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X31)
% 0.21/0.53          | ((k2_relat_1 @ X31) = (k1_relat_1 @ (k2_funct_1 @ X31)))
% 0.21/0.53          | ~ (v1_funct_1 @ X31)
% 0.21/0.53          | ~ (v1_relat_1 @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.53  thf(t182_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.53             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X1)
% 0.21/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.21/0.53              = (k10_relat_1 @ X2 @ (k1_relat_1 @ X1)))
% 0.21/0.53          | ~ (v1_relat_1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.53  thf(t54_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ A ) =>
% 0.21/0.53         ( ![B:$i]:
% 0.21/0.53           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.53             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.53               ( ( ![C:$i,D:$i]:
% 0.21/0.53                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.53                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.21/0.53                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.53                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.21/0.53                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.53                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.53                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.53                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.21/0.53                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, axiom,
% 0.21/0.53    (![D:$i,C:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.21/0.53       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.53         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.21/0.53         ((zip_tseitin_2 @ X17 @ X19 @ X20)
% 0.21/0.53          | ((X19) != (k1_funct_1 @ X20 @ X17))
% 0.21/0.53          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X20)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X17 : $i, X20 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X20))
% 0.21/0.53          | (zip_tseitin_2 @ X17 @ (k1_funct_1 @ X20 @ X17) @ X20))),
% 0.21/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (zip_tseitin_2 @ X2 @ (k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) @ 
% 0.21/0.53             (k5_relat_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | (zip_tseitin_2 @ X2 @ 
% 0.21/0.53             (k1_funct_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)) @ X2) @ 
% 0.21/0.53             (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | (zip_tseitin_2 @ X1 @ 
% 0.21/0.53             (k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1) @ 
% 0.21/0.53             (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | (zip_tseitin_2 @ X1 @ 
% 0.21/0.53             (k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1) @ 
% 0.21/0.53             (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (zip_tseitin_2 @ X1 @ 
% 0.21/0.53             (k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1) @ 
% 0.21/0.53             (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X0)
% 0.21/0.53          | (zip_tseitin_2 @ X1 @ 
% 0.21/0.53             (k1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1) @ 
% 0.21/0.53             (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.21/0.53          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | (zip_tseitin_2 @ sk_A @ 
% 0.21/0.53           (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A) @ 
% 0.21/0.53           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '14'])).
% 0.21/0.53  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((zip_tseitin_2 @ sk_A @ 
% 0.21/0.53        (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A) @ 
% 0.21/0.53        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.53         ((r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.21/0.53          | ~ (zip_tseitin_2 @ X17 @ X19 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((r2_hidden @ sk_A @ 
% 0.21/0.53        (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf(t22_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.53           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.53             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.21/0.53               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X4)
% 0.21/0.53          | ~ (v1_funct_1 @ X4)
% 0.21/0.53          | ((k1_funct_1 @ (k5_relat_1 @ X4 @ X5) @ X6)
% 0.21/0.53              = (k1_funct_1 @ X5 @ (k1_funct_1 @ X4 @ X6)))
% 0.21/0.53          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X5)))
% 0.21/0.53          | ~ (v1_funct_1 @ X5)
% 0.21/0.53          | ~ (v1_relat_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.53            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X17 : $i, X20 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X20))
% 0.21/0.53          | (zip_tseitin_2 @ X17 @ (k1_funct_1 @ X20 @ X17) @ X20))),
% 0.21/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X3 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.53          | ~ (v1_funct_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X3 : $i]:
% 0.21/0.53         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.53          | ~ (v1_funct_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.53  thf(zf_stmt_2, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_3, axiom,
% 0.21/0.53    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.21/0.53       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.21/0.53         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.53           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_6, axiom,
% 0.21/0.53    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.21/0.53       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.53         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.53           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_8, axiom,
% 0.21/0.53    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.53       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.53         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_9, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_1 @ A ) =>
% 0.21/0.53         ( ![B:$i]:
% 0.21/0.53           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.53               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.21/0.53                 ( ![C:$i,D:$i]:
% 0.21/0.53                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.21/0.53                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i, X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v2_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X27)
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ((X27) != (k2_funct_1 @ X26))
% 0.21/0.53          | (zip_tseitin_3 @ X30 @ X29 @ X27 @ X26)
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X26 : $i, X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X26)
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | (zip_tseitin_3 @ X30 @ X29 @ (k2_funct_1 @ X26) @ X26)
% 0.21/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X26))
% 0.21/0.53          | ~ (v2_funct_1 @ X26))),
% 0.21/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (zip_tseitin_2 @ X21 @ X22 @ X23)
% 0.21/0.53          | ((X21) = (k1_funct_1 @ X24 @ X22))
% 0.21/0.53          | ~ (zip_tseitin_3 @ X21 @ X22 @ X24 @ X23))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v2_funct_1 @ X0)
% 0.21/0.53          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.21/0.53          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((sk_A)
% 0.21/0.53          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '36'])).
% 0.21/0.53  thf('38', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (((sk_A)
% 0.21/0.53         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.53  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.53            = (sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['23', '41', '42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((sk_A)
% 0.21/0.53          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ((sk_A)
% 0.21/0.53            != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      ((((sk_A)
% 0.21/0.53          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((sk_A)
% 0.21/0.53                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.53                   sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (((sk_A)
% 0.21/0.53         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      ((((sk_A)
% 0.21/0.53          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.21/0.53         <= (~
% 0.21/0.53             (((sk_A)
% 0.21/0.53                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.53                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.21/0.53      inference('split', [status(esa)], ['45'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((((sk_A) != (sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((sk_A)
% 0.21/0.53                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.53                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((((sk_A)
% 0.21/0.53          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (~
% 0.21/0.53       (((sk_A)
% 0.21/0.53          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))) | 
% 0.21/0.53       ~
% 0.21/0.53       (((sk_A)
% 0.21/0.53          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['45'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (~
% 0.21/0.53       (((sk_A)
% 0.21/0.53          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (((sk_A)
% 0.21/0.53         != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['46', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['44', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '54'])).
% 0.21/0.53  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain, (~ (v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.53  thf('59', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '58'])).
% 0.21/0.53  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain, ($false),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
