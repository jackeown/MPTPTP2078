%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4bcusy1Lqw

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:34 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 316 expanded)
%              Number of leaves         :   31 ( 106 expanded)
%              Depth                    :   28
%              Number of atoms          : 1311 (7192 expanded)
%              Number of equality atoms :   88 ( 728 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

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

thf('3',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( X29 = X28 )
      | ( r2_hidden @ ( sk_C_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X29 ) )
      | ( ( k1_relat_1 @ X29 )
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_B
        = ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ X0 ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf(t57_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ X26 ) )
      | ( X27
        = ( k1_funct_1 @ X26 @ ( k1_funct_1 @ ( k2_funct_1 @ X26 ) @ X27 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t57_funct_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B )
      = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X31 )
        = X30 )
      | ( ( k1_funct_1 @ sk_A @ X30 )
       != X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X30: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ X30 ) )
        = X30 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X30 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X30: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ X30 ) )
        = X30 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ X30 ) @ ( k2_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X30 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('38',plain,
    ( ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B )
    = ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X21
       != ( k2_funct_1 @ X20 ) )
      | ( zip_tseitin_1 @ X22 @ X23 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('43',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( zip_tseitin_1 @ X22 @ X23 @ ( k2_funct_1 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('49',plain,(
    ! [X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X3 @ X1 @ X4 @ X5 )
      | ( X3
       != ( k1_funct_1 @ X4 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('50',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X5 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X4 @ X1 ) @ X1 @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X9 ) )
      | ~ ( zip_tseitin_1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','60'])).

thf('62',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( X29 = X28 )
      | ( ( k1_funct_1 @ X29 @ ( sk_C_1 @ X28 @ X29 ) )
       != ( k1_funct_1 @ X28 @ ( sk_C_1 @ X28 @ X29 ) ) )
      | ( ( k1_relat_1 @ X29 )
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('63',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k2_funct_1 @ sk_A ) @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    $false ),
    inference(simplify,[status(thm)],['83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4bcusy1Lqw
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 172 iterations in 0.079s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.38/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(t55_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ( v2_funct_1 @ A ) =>
% 0.38/0.59         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.59           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X25 : $i]:
% 0.38/0.59         (~ (v2_funct_1 @ X25)
% 0.38/0.59          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 0.38/0.59          | ~ (v1_funct_1 @ X25)
% 0.38/0.59          | ~ (v1_relat_1 @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.59  thf(dt_k2_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.59         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.59  thf(t60_funct_1, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.59           ( ( ( v2_funct_1 @ A ) & 
% 0.38/0.59               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.38/0.59               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.38/0.59               ( ![C:$i,D:$i]:
% 0.38/0.59                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.59                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.38/0.59                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.38/0.59                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.38/0.59             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.59              ( ( ( v2_funct_1 @ A ) & 
% 0.38/0.59                  ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.38/0.59                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.38/0.59                  ( ![C:$i,D:$i]:
% 0.38/0.59                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.59                        ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.38/0.59                      ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.38/0.59                        ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.38/0.59                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t60_funct_1])).
% 0.38/0.59  thf('3', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X25 : $i]:
% 0.38/0.59         (~ (v2_funct_1 @ X25)
% 0.38/0.59          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 0.38/0.59          | ~ (v1_funct_1 @ X25)
% 0.38/0.59          | ~ (v1_relat_1 @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.59  thf(t9_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.59           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.38/0.59               ( ![C:$i]:
% 0.38/0.59                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.38/0.59                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.38/0.59             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X28)
% 0.38/0.59          | ~ (v1_funct_1 @ X28)
% 0.38/0.59          | ((X29) = (X28))
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ X28 @ X29) @ (k1_relat_1 @ X29))
% 0.38/0.59          | ((k1_relat_1 @ X29) != (k1_relat_1 @ X28))
% 0.38/0.59          | ~ (v1_funct_1 @ X29)
% 0.38/0.59          | ~ (v1_relat_1 @ X29))),
% 0.38/0.59      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.38/0.59          | ((X1) = (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ((X1) = (k2_funct_1 @ X0))
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '8'])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.38/0.59          | ((X1) = (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ((X1) = (k2_funct_1 @ X0))
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['4', '10'])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X1)
% 0.38/0.59          | ~ (v1_funct_1 @ X1)
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.38/0.59          | ((X1) = (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ((sk_B) = (k2_funct_1 @ X0))
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ sk_B) @ 
% 0.38/0.59             (k1_relat_1 @ sk_B))
% 0.38/0.59          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.59          | ~ (v1_relat_1 @ sk_B)
% 0.38/0.59          | ~ (v2_funct_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '12'])).
% 0.38/0.59  thf('14', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ X0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ((sk_B) = (k2_funct_1 @ X0))
% 0.38/0.59          | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ X0) @ sk_B) @ 
% 0.38/0.59             (k2_relat_1 @ sk_A))
% 0.38/0.59          | ~ (v2_funct_1 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      ((~ (v2_funct_1 @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ 
% 0.38/0.59           (k2_relat_1 @ sk_A))
% 0.38/0.59        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.59      inference('eq_res', [status(thm)], ['17'])).
% 0.38/0.59  thf('19', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (((r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ 
% 0.38/0.59         (k2_relat_1 @ sk_A))
% 0.38/0.59        | ((sk_B) = (k2_funct_1 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.38/0.59  thf('23', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      ((r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.59  thf(t57_funct_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.59       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.38/0.59         ( ( ( A ) =
% 0.38/0.59             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.38/0.59           ( ( A ) =
% 0.38/0.59             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X26 : $i, X27 : $i]:
% 0.38/0.59         (~ (v2_funct_1 @ X26)
% 0.38/0.59          | ~ (r2_hidden @ X27 @ (k2_relat_1 @ X26))
% 0.38/0.59          | ((X27)
% 0.38/0.59              = (k1_funct_1 @ X26 @ (k1_funct_1 @ (k2_funct_1 @ X26) @ X27)))
% 0.38/0.59          | ~ (v1_funct_1 @ X26)
% 0.38/0.59          | ~ (v1_relat_1 @ X26))),
% 0.38/0.59      inference('cnf', [status(esa)], [t57_funct_1])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | ((sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)
% 0.38/0.59            = (k1_funct_1 @ sk_A @ 
% 0.38/0.59               (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59                (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))))
% 0.38/0.59        | ~ (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('28', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('29', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (((sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)
% 0.38/0.59         = (k1_funct_1 @ sk_A @ 
% 0.38/0.59            (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59             (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))))),
% 0.38/0.59      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X30 : $i, X31 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X30 @ (k1_relat_1 @ sk_A))
% 0.38/0.59          | ~ (r2_hidden @ X31 @ (k1_relat_1 @ sk_B))
% 0.38/0.59          | ((k1_funct_1 @ sk_B @ X31) = (X30))
% 0.38/0.59          | ((k1_funct_1 @ sk_A @ X30) != (X31)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X30 : $i]:
% 0.38/0.59         (((k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_A @ X30)) = (X30))
% 0.38/0.59          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ X30) @ (k1_relat_1 @ sk_B))
% 0.38/0.59          | ~ (r2_hidden @ X30 @ (k1_relat_1 @ sk_A)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.59  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('34', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X30 : $i]:
% 0.38/0.59         (((k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_A @ X30)) = (X30))
% 0.38/0.59          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ X30) @ (k2_relat_1 @ sk_A))
% 0.38/0.59          | ~ (r2_hidden @ X30 @ (k2_relat_1 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      ((~ (r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ 
% 0.38/0.59           (k2_relat_1 @ sk_A))
% 0.38/0.59        | ~ (r2_hidden @ 
% 0.38/0.59             (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59              (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59             (k2_relat_1 @ sk_B))
% 0.38/0.59        | ((k1_funct_1 @ sk_B @ 
% 0.38/0.59            (k1_funct_1 @ sk_A @ 
% 0.38/0.59             (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59              (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))))
% 0.38/0.59            = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59               (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['30', '35'])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      ((r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (((sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)
% 0.38/0.59         = (k1_funct_1 @ sk_A @ 
% 0.38/0.59            (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59             (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))))),
% 0.38/0.59      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      ((~ (r2_hidden @ 
% 0.38/0.59           (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59            (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59           (k2_relat_1 @ sk_B))
% 0.38/0.59        | ((k1_funct_1 @ sk_B @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.38/0.59            = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59               (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))))),
% 0.38/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.59  thf(t54_funct_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.38/0.59       ( ( v2_funct_1 @ A ) =>
% 0.38/0.59         ( ![B:$i]:
% 0.38/0.59           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.38/0.59             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.38/0.59               ( ( ![C:$i,D:$i]:
% 0.38/0.59                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.38/0.59                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.38/0.59                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.59                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.38/0.59                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.59                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.38/0.59                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.38/0.59                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.38/0.59                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_1, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.38/0.59  thf(zf_stmt_2, axiom,
% 0.38/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.59     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.38/0.59       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.38/0.59         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.38/0.59           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.38/0.59  thf(zf_stmt_4, axiom,
% 0.38/0.59    (![D:$i,C:$i,A:$i]:
% 0.38/0.59     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.38/0.59       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.59         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.38/0.59  thf(zf_stmt_6, axiom,
% 0.38/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.59     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.38/0.59       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.38/0.59         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.59           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.59  thf(zf_stmt_8, axiom,
% 0.38/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.59     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.38/0.59       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.38/0.59         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_9, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.59       ( ( v2_funct_1 @ A ) =>
% 0.38/0.59         ( ![B:$i]:
% 0.38/0.59           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.59             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.38/0.59               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.38/0.59                 ( ![C:$i,D:$i]:
% 0.38/0.59                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.38/0.59                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.59         (~ (v2_funct_1 @ X20)
% 0.38/0.59          | ~ (v1_relat_1 @ X21)
% 0.38/0.59          | ~ (v1_funct_1 @ X21)
% 0.38/0.59          | ((X21) != (k2_funct_1 @ X20))
% 0.38/0.59          | (zip_tseitin_1 @ X22 @ X23 @ X21 @ X20)
% 0.38/0.59          | ~ (v1_funct_1 @ X20)
% 0.38/0.59          | ~ (v1_relat_1 @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X20)
% 0.38/0.59          | ~ (v1_funct_1 @ X20)
% 0.38/0.59          | (zip_tseitin_1 @ X22 @ X23 @ (k2_funct_1 @ X20) @ X20)
% 0.38/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X20))
% 0.38/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X20))
% 0.38/0.59          | ~ (v2_funct_1 @ X20))),
% 0.38/0.59      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['41', '43'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['40', '45'])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['46'])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      ((r2_hidden @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.59         ((zip_tseitin_0 @ X3 @ X1 @ X4 @ X5)
% 0.38/0.59          | ((X3) != (k1_funct_1 @ X4 @ X1))
% 0.38/0.59          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X5)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X5))
% 0.38/0.59          | (zip_tseitin_0 @ (k1_funct_1 @ X4 @ X1) @ X1 @ X4 @ X5))),
% 0.38/0.59      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (zip_tseitin_0 @ 
% 0.38/0.59          (k1_funct_1 @ X0 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59          (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ X0 @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['48', '50'])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.59         (~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.38/0.59          | (r2_hidden @ X6 @ (k1_relat_1 @ X9))
% 0.38/0.59          | ~ (zip_tseitin_1 @ X6 @ X7 @ X8 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (zip_tseitin_1 @ 
% 0.38/0.59             (k1_funct_1 @ X0 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59             (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ X0 @ sk_A)
% 0.38/0.59          | (r2_hidden @ 
% 0.38/0.59             (k1_funct_1 @ X0 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59             (k1_relat_1 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.59  thf('54', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('55', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (zip_tseitin_1 @ 
% 0.38/0.59             (k1_funct_1 @ X0 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59             (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B) @ X0 @ sk_A)
% 0.38/0.59          | (r2_hidden @ 
% 0.38/0.59             (k1_funct_1 @ X0 @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59             (k2_relat_1 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v2_funct_1 @ sk_A)
% 0.38/0.59        | (r2_hidden @ 
% 0.38/0.59           (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59            (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59           (k2_relat_1 @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['47', '55'])).
% 0.38/0.59  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('58', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('59', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      ((r2_hidden @ 
% 0.38/0.59        (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59         (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)) @ 
% 0.38/0.59        (k2_relat_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.38/0.59  thf('61', plain,
% 0.38/0.59      (((k1_funct_1 @ sk_B @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.38/0.59         = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ 
% 0.38/0.59            (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['39', '60'])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X28)
% 0.38/0.59          | ~ (v1_funct_1 @ X28)
% 0.38/0.59          | ((X29) = (X28))
% 0.38/0.59          | ((k1_funct_1 @ X29 @ (sk_C_1 @ X28 @ X29))
% 0.38/0.59              != (k1_funct_1 @ X28 @ (sk_C_1 @ X28 @ X29)))
% 0.38/0.59          | ((k1_relat_1 @ X29) != (k1_relat_1 @ X28))
% 0.38/0.59          | ~ (v1_funct_1 @ X29)
% 0.38/0.59          | ~ (v1_relat_1 @ X29))),
% 0.38/0.59      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.38/0.59          != (k1_funct_1 @ sk_B @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.59        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.38/0.59        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.59  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('66', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('67', plain,
% 0.38/0.59      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B))
% 0.38/0.59          != (k1_funct_1 @ sk_B @ (sk_C_1 @ (k2_funct_1 @ sk_A) @ sk_B)))
% 0.38/0.59        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.38/0.59        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.38/0.59        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.38/0.59        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['67'])).
% 0.38/0.59  thf('69', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('70', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.38/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.38/0.59        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.38/0.59  thf('71', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.38/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '70'])).
% 0.38/0.59  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('73', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('74', plain,
% 0.38/0.59      ((((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.38/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.38/0.59  thf('75', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '74'])).
% 0.38/0.59  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('77', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('78', plain,
% 0.38/0.59      (((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.38/0.59  thf('79', plain,
% 0.38/0.59      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.59        | ~ (v2_funct_1 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['0', '78'])).
% 0.38/0.59  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('81', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('82', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('83', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.38/0.59  thf('84', plain, ($false), inference('simplify', [status(thm)], ['83'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
