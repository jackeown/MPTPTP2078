%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q2VgReSGiW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 226 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :   22
%              Number of atoms          : 1079 (3275 expanded)
%              Number of equality atoms :   48 ( 190 expanded)
%              Maximal formula depth    :   16 (   7 average)

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
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
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

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( X27
       != ( k2_funct_1 @ X26 ) )
      | ( zip_tseitin_1 @ X28 @ X29 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('7',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( zip_tseitin_1 @ X28 @ X29 @ ( k2_funct_1 @ X26 ) @ X26 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X26 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

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

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('13',plain,(
    ! [X7: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X9 @ X7 @ X10 @ X11 )
      | ( X9
       != ( k1_funct_1 @ X10 @ X7 ) )
      | ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('14',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X11 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X10 @ X7 ) @ X7 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('21',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

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

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X3 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,(
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
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('31',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X26 ) )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X26 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_2 @ X17 @ X19 @ X20 )
      | ( X19
       != ( k1_funct_1 @ X20 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X17: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X20 ) )
      | ( zip_tseitin_2 @ X17 @ ( k1_funct_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('43',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

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

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) @ X6 )
        = ( k1_funct_1 @ X5 @ ( k1_funct_1 @ X4 @ X6 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('60',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X13
        = ( k1_funct_1 @ X15 @ X12 ) )
      | ~ ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B )
      | ( sk_A
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('66',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('67',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','67'])).

thf('69',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('70',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('72',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['69'])).

thf('73',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['69'])).

thf('76',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','76'])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','77'])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('82',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('85',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['83','84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q2VgReSGiW
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 73 iterations in 0.026s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.47  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.47  thf(dt_k2_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.47         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf(t54_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ A ) =>
% 0.20/0.47         ( ![B:$i]:
% 0.20/0.47           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.47             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.47               ( ( ![C:$i,D:$i]:
% 0.20/0.47                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.47                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.20/0.47                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.47                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.20/0.47                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.47                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.47                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.47                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.20/0.47                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_1, axiom,
% 0.20/0.47    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.20/0.47       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.20/0.47         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.47           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_3, axiom,
% 0.20/0.47    (![D:$i,C:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.20/0.47       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.47         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_5, axiom,
% 0.20/0.47    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.20/0.47       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.20/0.47         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.47           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_7, axiom,
% 0.20/0.47    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.47       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.47         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_8, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ A ) =>
% 0.20/0.47         ( ![B:$i]:
% 0.20/0.47           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.47               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.20/0.47                 ( ![C:$i,D:$i]:
% 0.20/0.47                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.20/0.47                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.47         (~ (v2_funct_1 @ X26)
% 0.20/0.47          | ~ (v1_relat_1 @ X27)
% 0.20/0.47          | ~ (v1_funct_1 @ X27)
% 0.20/0.47          | ((X27) != (k2_funct_1 @ X26))
% 0.20/0.47          | (zip_tseitin_1 @ X28 @ X29 @ X27 @ X26)
% 0.20/0.47          | ~ (v1_funct_1 @ X26)
% 0.20/0.47          | ~ (v1_relat_1 @ X26))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X26)
% 0.20/0.47          | ~ (v1_funct_1 @ X26)
% 0.20/0.47          | (zip_tseitin_1 @ X28 @ X29 @ (k2_funct_1 @ X26) @ X26)
% 0.20/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.20/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X26))
% 0.20/0.47          | ~ (v2_funct_1 @ X26))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf(t57_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.47         ( ( ( A ) =
% 0.20/0.47             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.47           ( ( A ) =
% 0.20/0.47             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_9, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.47            ( ( ( A ) =
% 0.20/0.47                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.47              ( ( A ) =
% 0.20/0.47                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.20/0.47  thf('12', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X7 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X9 @ X7 @ X10 @ X11)
% 0.20/0.47          | ((X9) != (k1_funct_1 @ X10 @ X7))
% 0.20/0.47          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X11)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X7 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X7 @ (k2_relat_1 @ X11))
% 0.20/0.47          | (zip_tseitin_0 @ (k1_funct_1 @ X10 @ X7) @ X7 @ X10 @ X11))),
% 0.20/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (zip_tseitin_0 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.20/0.47          | (r2_hidden @ X12 @ (k1_relat_1 @ X15))
% 0.20/0.47          | ~ (zip_tseitin_1 @ X12 @ X13 @ X14 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (zip_tseitin_1 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.47        | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.20/0.47           (k1_relat_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '17'])).
% 0.20/0.47  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('21', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.20/0.47        (k1_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.20/0.47  thf(t21_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.20/0.47             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.47               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (v1_funct_1 @ X1)
% 0.20/0.47          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.20/0.47          | ~ (r2_hidden @ (k1_funct_1 @ X1 @ X2) @ (k1_relat_1 @ X3))
% 0.20/0.47          | (r2_hidden @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X3)))
% 0.20/0.47          | ~ (v1_funct_1 @ X3)
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | (r2_hidden @ sk_A @ 
% 0.20/0.47           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))
% 0.20/0.47        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.20/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('27', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X26 : $i, X27 : $i]:
% 0.20/0.47         (~ (v2_funct_1 @ X26)
% 0.20/0.47          | ~ (v1_relat_1 @ X27)
% 0.20/0.47          | ~ (v1_funct_1 @ X27)
% 0.20/0.47          | ((X27) != (k2_funct_1 @ X26))
% 0.20/0.47          | ((k1_relat_1 @ X27) = (k2_relat_1 @ X26))
% 0.20/0.47          | ~ (v1_funct_1 @ X26)
% 0.20/0.47          | ~ (v1_relat_1 @ X26))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X26 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X26)
% 0.20/0.47          | ~ (v1_funct_1 @ X26)
% 0.20/0.47          | ((k1_relat_1 @ (k2_funct_1 @ X26)) = (k2_relat_1 @ X26))
% 0.20/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.20/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X26))
% 0.20/0.47          | ~ (v2_funct_1 @ X26))),
% 0.20/0.47      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.20/0.47         ((zip_tseitin_2 @ X17 @ X19 @ X20)
% 0.20/0.47          | ((X19) != (k1_funct_1 @ X20 @ X17))
% 0.20/0.47          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X20)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X17 : $i, X20 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X20))
% 0.20/0.47          | (zip_tseitin_2 @ X17 @ (k1_funct_1 @ X20 @ X17) @ X20))),
% 0.20/0.47      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | (zip_tseitin_2 @ X1 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 0.20/0.47             (k2_funct_1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.20/0.47         (k2_funct_1 @ sk_B))
% 0.20/0.47        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '38'])).
% 0.20/0.47  thf('40', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      ((zip_tseitin_2 @ sk_A @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.20/0.47        (k2_funct_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.47         ((r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.20/0.47          | ~ (zip_tseitin_2 @ X17 @ X19 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('45', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (((r2_hidden @ sk_A @ 
% 0.20/0.47         (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))
% 0.20/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['24', '25', '26', '45'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.47        | (r2_hidden @ sk_A @ 
% 0.20/0.47           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '46'])).
% 0.20/0.47  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.47        | (r2_hidden @ sk_A @ 
% 0.20/0.47           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))))),
% 0.20/0.47      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | (r2_hidden @ sk_A @ 
% 0.20/0.47           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '50'])).
% 0.20/0.47  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      ((r2_hidden @ sk_A @ 
% 0.20/0.47        (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.47  thf(t22_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.20/0.47             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.20/0.47               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ((k1_funct_1 @ (k5_relat_1 @ X4 @ X5) @ X6)
% 0.20/0.47              = (k1_funct_1 @ X5 @ (k1_funct_1 @ X4 @ X6)))
% 0.20/0.47          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ (k5_relat_1 @ X4 @ X5)))
% 0.20/0.47          | ~ (v1_funct_1 @ X5)
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.20/0.47            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.47  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('59', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.47          | ~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf('60', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (zip_tseitin_0 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.47  thf('61', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.20/0.47          | ((X13) = (k1_funct_1 @ X15 @ X12))
% 0.20/0.47          | ~ (zip_tseitin_1 @ X12 @ X13 @ X14 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (zip_tseitin_1 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)
% 0.20/0.47          | ((sk_A) = (k1_funct_1 @ sk_B @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.47  thf('63', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.47        | ((sk_A)
% 0.20/0.47            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['59', '62'])).
% 0.20/0.47  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('66', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('67', plain,
% 0.20/0.47      (((sk_A)
% 0.20/0.47         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.20/0.47  thf('68', plain,
% 0.20/0.47      ((((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.20/0.47          = (sk_A))
% 0.20/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['56', '57', '58', '67'])).
% 0.20/0.47  thf('69', plain,
% 0.20/0.47      ((((sk_A)
% 0.20/0.47          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.47        | ((sk_A)
% 0.20/0.47            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('70', plain,
% 0.20/0.47      ((((sk_A)
% 0.20/0.47          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((sk_A)
% 0.20/0.47                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.20/0.47                   sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['69'])).
% 0.20/0.47  thf('71', plain,
% 0.20/0.47      (((sk_A)
% 0.20/0.47         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.20/0.47  thf('72', plain,
% 0.20/0.47      ((((sk_A)
% 0.20/0.47          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((sk_A)
% 0.20/0.47                = (k1_funct_1 @ sk_B @ 
% 0.20/0.47                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.20/0.47      inference('split', [status(esa)], ['69'])).
% 0.20/0.47  thf('73', plain,
% 0.20/0.47      ((((sk_A) != (sk_A)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((sk_A)
% 0.20/0.47                = (k1_funct_1 @ sk_B @ 
% 0.20/0.47                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.47  thf('74', plain,
% 0.20/0.47      ((((sk_A)
% 0.20/0.47          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.47  thf('75', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((sk_A)
% 0.20/0.47          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.20/0.47       ~
% 0.20/0.47       (((sk_A)
% 0.20/0.47          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['69'])).
% 0.20/0.47  thf('76', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((sk_A)
% 0.20/0.47          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.20/0.47  thf('77', plain,
% 0.20/0.47      (((sk_A)
% 0.20/0.47         != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['70', '76'])).
% 0.20/0.47  thf('78', plain,
% 0.20/0.47      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['68', '77'])).
% 0.20/0.47  thf('79', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '78'])).
% 0.20/0.47  thf('80', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('82', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.20/0.47  thf('83', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '82'])).
% 0.20/0.47  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('85', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.47  thf('86', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
