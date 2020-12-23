%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mt3gUeWHZe

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 219 expanded)
%              Number of leaves         :   29 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          : 1036 (3211 expanded)
%              Number of equality atoms :   47 ( 188 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('4',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
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
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_2 @ X17 @ X19 @ X20 )
      | ( X19
       != ( k1_funct_1 @ X20 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X17: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) )
      | ( zip_tseitin_2 @ X17 @ ( k1_funct_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('10',plain,(
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

thf('11',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( zip_tseitin_3 @ X30 @ X29 @ ( k2_funct_1 @ X26 ) @ X26 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X26 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_2 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ ( k2_relat_1 @ X23 ) )
      | ~ ( zip_tseitin_3 @ X21 @ X22 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('25',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( X27
       != ( k2_funct_1 @ X26 ) )
      | ( ( k1_relat_1 @ X27 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('26',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X26 ) )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X26 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X3 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

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

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) @ X6 )
        = ( k1_funct_1 @ X5 @ ( k1_funct_1 @ X4 @ X6 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['4','6'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_2 @ X21 @ X22 @ X23 )
      | ( X21
        = ( k1_funct_1 @ X24 @ X22 ) )
      | ~ ( zip_tseitin_3 @ X21 @ X22 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['50','59','60','61'])).

thf('63',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('66',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('67',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('70',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['64','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['77','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mt3gUeWHZe
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 72 iterations in 0.049s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.54  thf(dt_k2_funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf(t56_funct_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.54         ( ( ( A ) =
% 0.21/0.54             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.54           ( ( A ) =
% 0.21/0.54             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.54            ( ( ( A ) =
% 0.21/0.54                ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.54              ( ( A ) =
% 0.21/0.54                ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t56_funct_1])).
% 0.21/0.54  thf('4', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
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
% 0.21/0.54  thf(zf_stmt_1, axiom,
% 0.21/0.54    (![D:$i,C:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.21/0.54       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.54         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         ((zip_tseitin_2 @ X17 @ X19 @ X20)
% 0.21/0.54          | ((X19) != (k1_funct_1 @ X20 @ X17))
% 0.21/0.54          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X20)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X17 : $i, X20 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X20))
% 0.21/0.54          | (zip_tseitin_2 @ X17 @ (k1_funct_1 @ X20 @ X17) @ X20))),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf('7', plain, ((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf(zf_stmt_2, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_3, axiom,
% 0.21/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.21/0.54       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.21/0.54         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.54           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_6, axiom,
% 0.21/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.21/0.54       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.54         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.54           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_8, axiom,
% 0.21/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.54       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.54         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_9, axiom,
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
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i, X29 : $i, X30 : $i]:
% 0.21/0.54         (~ (v2_funct_1 @ X26)
% 0.21/0.54          | ~ (v1_relat_1 @ X27)
% 0.21/0.54          | ~ (v1_funct_1 @ X27)
% 0.21/0.54          | ((X27) != (k2_funct_1 @ X26))
% 0.21/0.54          | (zip_tseitin_3 @ X30 @ X29 @ X27 @ X26)
% 0.21/0.54          | ~ (v1_funct_1 @ X26)
% 0.21/0.54          | ~ (v1_relat_1 @ X26))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X26 : $i, X29 : $i, X30 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X26)
% 0.21/0.54          | ~ (v1_funct_1 @ X26)
% 0.21/0.54          | (zip_tseitin_3 @ X30 @ X29 @ (k2_funct_1 @ X26) @ X26)
% 0.21/0.54          | ~ (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X26))
% 0.21/0.54          | ~ (v2_funct_1 @ X26))),
% 0.21/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.54         (~ (zip_tseitin_2 @ X21 @ X22 @ X23)
% 0.21/0.54          | (r2_hidden @ X22 @ (k2_relat_1 @ X23))
% 0.21/0.54          | ~ (zip_tseitin_3 @ X21 @ X22 @ X24 @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.21/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '17'])).
% 0.21/0.54  thf('19', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i]:
% 0.21/0.54         (~ (v2_funct_1 @ X26)
% 0.21/0.54          | ~ (v1_relat_1 @ X27)
% 0.21/0.54          | ~ (v1_funct_1 @ X27)
% 0.21/0.54          | ((X27) != (k2_funct_1 @ X26))
% 0.21/0.54          | ((k1_relat_1 @ X27) = (k2_relat_1 @ X26))
% 0.21/0.54          | ~ (v1_funct_1 @ X26)
% 0.21/0.54          | ~ (v1_relat_1 @ X26))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X26 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X26)
% 0.21/0.54          | ~ (v1_funct_1 @ X26)
% 0.21/0.54          | ((k1_relat_1 @ (k2_funct_1 @ X26)) = (k2_relat_1 @ X26))
% 0.21/0.54          | ~ (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X26))
% 0.21/0.54          | ~ (v2_funct_1 @ X26))),
% 0.21/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf(t21_funct_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.21/0.54             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.54               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_funct_1 @ X1)
% 0.21/0.54          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.21/0.54          | ~ (r2_hidden @ (k1_funct_1 @ X1 @ X2) @ (k1_relat_1 @ X3))
% 0.21/0.54          | (r2_hidden @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X3)))
% 0.21/0.54          | ~ (v1_funct_1 @ X3)
% 0.21/0.54          | ~ (v1_relat_1 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r2_hidden @ (k1_funct_1 @ X2 @ X1) @ (k2_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.54          | (r2_hidden @ X1 @ 
% 0.21/0.54             (k1_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X0))))
% 0.21/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X2))
% 0.21/0.54          | ~ (v1_funct_1 @ X2)
% 0.21/0.54          | ~ (v1_relat_1 @ X2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))
% 0.21/0.54        | (r2_hidden @ sk_A @ 
% 0.21/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '32'])).
% 0.21/0.54  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('37', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (((r2_hidden @ sk_A @ 
% 0.21/0.54         (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['33', '34', '35', '36', '37', '38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | (r2_hidden @ sk_A @ 
% 0.21/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '40'])).
% 0.21/0.54  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | (r2_hidden @ sk_A @ 
% 0.21/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | (r2_hidden @ sk_A @ 
% 0.21/0.54           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '44'])).
% 0.21/0.54  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((r2_hidden @ sk_A @ 
% 0.21/0.54        (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.54  thf(t22_funct_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.54             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.21/0.54               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X4)
% 0.21/0.54          | ~ (v1_funct_1 @ X4)
% 0.21/0.54          | ((k1_funct_1 @ (k5_relat_1 @ X4 @ X5) @ X6)
% 0.21/0.54              = (k1_funct_1 @ X5 @ (k1_funct_1 @ X4 @ X6)))
% 0.21/0.54          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X5)))
% 0.21/0.54          | ~ (v1_funct_1 @ X5)
% 0.21/0.54          | ~ (v1_relat_1 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.54            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.54         (~ (zip_tseitin_2 @ X21 @ X22 @ X23)
% 0.21/0.54          | ((X21) = (k1_funct_1 @ X24 @ X22))
% 0.21/0.54          | ~ (zip_tseitin_3 @ X21 @ X22 @ X24 @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v2_funct_1 @ X0)
% 0.21/0.54          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.21/0.54          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['51', '54'])).
% 0.21/0.54  thf('56', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (((sk_A)
% 0.21/0.54         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.54  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.21/0.54            = (sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['50', '59', '60', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.54        | ((sk_A)
% 0.21/0.54            != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.21/0.54                   sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['63'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((sk_A)
% 0.21/0.54         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.54                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.21/0.54      inference('split', [status(esa)], ['63'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((((sk_A) != (sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((sk_A)
% 0.21/0.54                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.54                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((((sk_A)
% 0.21/0.54          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (~
% 0.21/0.54       (((sk_A)
% 0.21/0.54          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))) | 
% 0.21/0.54       ~
% 0.21/0.54       (((sk_A)
% 0.21/0.54          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['63'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (~
% 0.21/0.54       (((sk_A)
% 0.21/0.54          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (((sk_A)
% 0.21/0.54         != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['64', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['62', '71'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '72'])).
% 0.21/0.54  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('76', plain, (~ (v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.21/0.54  thf('77', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '76'])).
% 0.21/0.54  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('80', plain, ($false),
% 0.21/0.54      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
