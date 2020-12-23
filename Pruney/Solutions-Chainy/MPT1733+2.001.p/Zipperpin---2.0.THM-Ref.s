%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jGpy2vM5KY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:34 EST 2020

% Result     : Theorem 5.55s
% Output     : Refutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  201 (1274 expanded)
%              Number of leaves         :   22 ( 347 expanded)
%              Depth                    :   41
%              Number of atoms          : 2345 (35712 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(t42_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ~ ( r1_tsep_1 @ B @ C )
                   => ( ( ( ( r1_tsep_1 @ B @ D )
                          | ( r1_tsep_1 @ C @ D ) )
                       => ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) )
                      & ( ( ( r1_tsep_1 @ D @ B )
                          | ( r1_tsep_1 @ D @ C ) )
                       => ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ~ ( r1_tsep_1 @ B @ C )
                     => ( ( ( ( r1_tsep_1 @ B @ D )
                            | ( r1_tsep_1 @ C @ D ) )
                         => ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) )
                        & ( ( ( r1_tsep_1 @ D @ B )
                            | ( r1_tsep_1 @ D @ C ) )
                         => ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ( ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ B )
                  & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ C ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( r1_tsep_1 @ X11 @ X13 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X1 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t23_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( m1_pre_topc @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( m1_pre_topc @ C @ A )
                & ~ ( v2_struct_0 @ C ) )
             => ! [D: $i] :
                  ( ( ( m1_pre_topc @ D @ A )
                    & ~ ( v2_struct_0 @ D ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ~ ( r1_tsep_1 @ D @ C )
                        & ~ ( r1_tsep_1 @ C @ D ) )
                      | ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ B @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_1 @ D @ B )
     => ( ( r1_tsep_1 @ B @ D )
        & ( r1_tsep_1 @ D @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i] :
      ( ( zip_tseitin_0 @ D @ C )
     => ( ~ ( r1_tsep_1 @ C @ D )
        & ~ ( r1_tsep_1 @ D @ C ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( zip_tseitin_1 @ D @ B )
                      | ( zip_tseitin_0 @ D @ C ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( zip_tseitin_0 @ X9 @ X10 )
      | ( zip_tseitin_1 @ X9 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( zip_tseitin_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tsep_1 @ X6 @ X5 )
      | ~ ( zip_tseitin_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( r1_tsep_1 @ X11 @ X13 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tsep_1 @ X6 @ X5 )
      | ~ ( zip_tseitin_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['30'])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tsep_1 @ X3 @ X4 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('64',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tsep_1 @ X5 @ X6 )
      | ~ ( zip_tseitin_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['30'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['30'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tsep_1 @ X5 @ X6 )
      | ~ ( zip_tseitin_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('101',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['30'])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('114',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tsep_1 @ X3 @ X4 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('115',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['33','73','97','98','124'])).

thf('126',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['31','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['137'])).

thf('139',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tsep_1 @ X4 @ X3 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('140',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['136','140'])).

thf('142',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('144',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['137'])).

thf('145',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tsep_1 @ X4 @ X3 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('146',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('157',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['167'])).

thf('169',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['142','124','155','73','97','98','166','168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['141','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['0','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jGpy2vM5KY
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.55/5.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.55/5.74  % Solved by: fo/fo7.sh
% 5.55/5.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.55/5.74  % done 1216 iterations in 5.282s
% 5.55/5.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.55/5.74  % SZS output start Refutation
% 5.55/5.74  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 5.55/5.74  thf(sk_D_type, type, sk_D: $i).
% 5.55/5.74  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 5.55/5.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.55/5.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.55/5.74  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 5.55/5.74  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 5.55/5.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.55/5.74  thf(sk_B_type, type, sk_B: $i).
% 5.55/5.74  thf(sk_A_type, type, sk_A: $i).
% 5.55/5.74  thf(sk_C_type, type, sk_C: $i).
% 5.55/5.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.55/5.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 5.55/5.74  thf(t42_tmap_1, conjecture,
% 5.55/5.74    (![A:$i]:
% 5.55/5.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.55/5.74       ( ![B:$i]:
% 5.55/5.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.55/5.74           ( ![C:$i]:
% 5.55/5.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.55/5.74               ( ![D:$i]:
% 5.55/5.74                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.55/5.74                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 5.55/5.74                     ( ( ( ( r1_tsep_1 @ B @ D ) | ( r1_tsep_1 @ C @ D ) ) =>
% 5.55/5.74                         ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 5.55/5.74                       ( ( ( r1_tsep_1 @ D @ B ) | ( r1_tsep_1 @ D @ C ) ) =>
% 5.55/5.74                         ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.55/5.74  thf(zf_stmt_0, negated_conjecture,
% 5.55/5.74    (~( ![A:$i]:
% 5.55/5.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.55/5.74            ( l1_pre_topc @ A ) ) =>
% 5.55/5.74          ( ![B:$i]:
% 5.55/5.74            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.55/5.74              ( ![C:$i]:
% 5.55/5.74                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.55/5.74                  ( ![D:$i]:
% 5.55/5.74                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.55/5.74                      ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 5.55/5.74                        ( ( ( ( r1_tsep_1 @ B @ D ) | ( r1_tsep_1 @ C @ D ) ) =>
% 5.55/5.74                            ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 5.55/5.74                          ( ( ( r1_tsep_1 @ D @ B ) | ( r1_tsep_1 @ D @ C ) ) =>
% 5.55/5.74                            ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 5.55/5.74    inference('cnf.neg', [status(esa)], [t42_tmap_1])).
% 5.55/5.74  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf(t30_tsep_1, axiom,
% 5.55/5.74    (![A:$i]:
% 5.55/5.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.55/5.74       ( ![B:$i]:
% 5.55/5.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.55/5.74           ( ![C:$i]:
% 5.55/5.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.55/5.74               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 5.55/5.74                 ( ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ B ) & 
% 5.55/5.74                   ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ C ) ) ) ) ) ) ) ))).
% 5.55/5.74  thf('4', plain,
% 5.55/5.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.55/5.74         ((v2_struct_0 @ X11)
% 5.55/5.74          | ~ (m1_pre_topc @ X11 @ X12)
% 5.55/5.74          | (r1_tsep_1 @ X11 @ X13)
% 5.55/5.74          | (m1_pre_topc @ (k2_tsep_1 @ X12 @ X11 @ X13) @ X13)
% 5.55/5.74          | ~ (m1_pre_topc @ X13 @ X12)
% 5.55/5.74          | (v2_struct_0 @ X13)
% 5.55/5.74          | ~ (l1_pre_topc @ X12)
% 5.55/5.74          | ~ (v2_pre_topc @ X12)
% 5.55/5.74          | (v2_struct_0 @ X12))),
% 5.55/5.74      inference('cnf', [status(esa)], [t30_tsep_1])).
% 5.55/5.74  thf('5', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | ~ (v2_pre_topc @ sk_A)
% 5.55/5.74          | ~ (l1_pre_topc @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X0)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_B))),
% 5.55/5.74      inference('sup-', [status(thm)], ['3', '4'])).
% 5.55/5.74  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('8', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X0)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_B))),
% 5.55/5.74      inference('demod', [status(thm)], ['5', '6', '7'])).
% 5.55/5.74  thf('9', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_B)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_A))),
% 5.55/5.74      inference('sup-', [status(thm)], ['2', '8'])).
% 5.55/5.74  thf('10', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('11', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf(dt_k2_tsep_1, axiom,
% 5.55/5.74    (![A:$i,B:$i,C:$i]:
% 5.55/5.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 5.55/5.74         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 5.55/5.74         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.55/5.74       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 5.55/5.74         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 5.55/5.74         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 5.55/5.74  thf('12', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.74         (~ (m1_pre_topc @ X0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (l1_pre_topc @ X1)
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X2)
% 5.55/5.74          | ~ (m1_pre_topc @ X2 @ X1)
% 5.55/5.74          | (m1_pre_topc @ (k2_tsep_1 @ X1 @ X0 @ X2) @ X1))),
% 5.55/5.74      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 5.55/5.74  thf('13', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | ~ (l1_pre_topc @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B))),
% 5.55/5.74      inference('sup-', [status(thm)], ['11', '12'])).
% 5.55/5.74  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('15', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B))),
% 5.55/5.74      inference('demod', [status(thm)], ['13', '14'])).
% 5.55/5.74  thf('16', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_B)
% 5.55/5.74        | (v2_struct_0 @ sk_A)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 5.55/5.74      inference('sup-', [status(thm)], ['10', '15'])).
% 5.55/5.74  thf(t23_tmap_1, axiom,
% 5.55/5.74    (![A:$i]:
% 5.55/5.74     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 5.55/5.74       ( ![B:$i]:
% 5.55/5.74         ( ( ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 5.55/5.74           ( ![C:$i]:
% 5.55/5.74             ( ( ( m1_pre_topc @ C @ A ) & ( ~( v2_struct_0 @ C ) ) ) =>
% 5.55/5.74               ( ![D:$i]:
% 5.55/5.74                 ( ( ( m1_pre_topc @ D @ A ) & ( ~( v2_struct_0 @ D ) ) ) =>
% 5.55/5.74                   ( ( m1_pre_topc @ B @ C ) =>
% 5.55/5.74                     ( ( ( ~( r1_tsep_1 @ D @ C ) ) & 
% 5.55/5.74                         ( ~( r1_tsep_1 @ C @ D ) ) ) | 
% 5.55/5.74                       ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 5.55/5.74  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 5.55/5.74  thf(zf_stmt_2, axiom,
% 5.55/5.74    (![D:$i,B:$i]:
% 5.55/5.74     ( ( zip_tseitin_1 @ D @ B ) =>
% 5.55/5.74       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ))).
% 5.55/5.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.55/5.74  thf(zf_stmt_4, axiom,
% 5.55/5.74    (![D:$i,C:$i]:
% 5.55/5.74     ( ( zip_tseitin_0 @ D @ C ) =>
% 5.55/5.74       ( ( ~( r1_tsep_1 @ C @ D ) ) & ( ~( r1_tsep_1 @ D @ C ) ) ) ))).
% 5.55/5.74  thf(zf_stmt_5, axiom,
% 5.55/5.74    (![A:$i]:
% 5.55/5.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.55/5.74       ( ![B:$i]:
% 5.55/5.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.55/5.74           ( ![C:$i]:
% 5.55/5.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.55/5.74               ( ![D:$i]:
% 5.55/5.74                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.55/5.74                   ( ( m1_pre_topc @ B @ C ) =>
% 5.55/5.74                     ( ( zip_tseitin_1 @ D @ B ) | ( zip_tseitin_0 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 5.55/5.74  thf('17', plain,
% 5.55/5.74      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 5.55/5.74         ((v2_struct_0 @ X7)
% 5.55/5.74          | ~ (m1_pre_topc @ X7 @ X8)
% 5.55/5.74          | (v2_struct_0 @ X9)
% 5.55/5.74          | ~ (m1_pre_topc @ X9 @ X8)
% 5.55/5.74          | (zip_tseitin_0 @ X9 @ X10)
% 5.55/5.74          | (zip_tseitin_1 @ X9 @ X7)
% 5.55/5.74          | ~ (m1_pre_topc @ X7 @ X10)
% 5.55/5.74          | ~ (m1_pre_topc @ X10 @ X8)
% 5.55/5.74          | (v2_struct_0 @ X10)
% 5.55/5.74          | ~ (l1_pre_topc @ X8)
% 5.55/5.74          | ~ (v2_pre_topc @ X8)
% 5.55/5.74          | (v2_struct_0 @ X8))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.55/5.74  thf('18', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | ~ (v2_pre_topc @ sk_A)
% 5.55/5.74          | ~ (l1_pre_topc @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 5.55/5.74          | (zip_tseitin_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (zip_tseitin_0 @ X1 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['16', '17'])).
% 5.55/5.74  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('21', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 5.55/5.74          | (zip_tseitin_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (zip_tseitin_0 @ X1 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('demod', [status(thm)], ['18', '19', '20'])).
% 5.55/5.74  thf('22', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i]:
% 5.55/5.74         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 5.55/5.74          | (zip_tseitin_0 @ X1 @ X0)
% 5.55/5.74          | (zip_tseitin_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_C))),
% 5.55/5.74      inference('simplify', [status(thm)], ['21'])).
% 5.55/5.74  thf('23', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 5.55/5.74          | (zip_tseitin_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (zip_tseitin_0 @ X0 @ sk_C)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['9', '22'])).
% 5.55/5.74  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('25', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (zip_tseitin_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (zip_tseitin_0 @ X0 @ sk_C)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('demod', [status(thm)], ['23', '24'])).
% 5.55/5.74  thf('26', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (zip_tseitin_0 @ X0 @ sk_C)
% 5.55/5.74          | (zip_tseitin_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A))),
% 5.55/5.74      inference('simplify', [status(thm)], ['25'])).
% 5.55/5.74  thf('27', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_A)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (zip_tseitin_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['1', '26'])).
% 5.55/5.74  thf('28', plain,
% 5.55/5.74      (![X5 : $i, X6 : $i]:
% 5.55/5.74         ((r1_tsep_1 @ X6 @ X5) | ~ (zip_tseitin_1 @ X6 @ X5))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.55/5.74  thf('29', plain,
% 5.55/5.74      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_A)
% 5.55/5.74        | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['27', '28'])).
% 5.55/5.74  thf('30', plain,
% 5.55/5.74      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 5.55/5.74        | ~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('31', plain,
% 5.55/5.74      ((~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.74      inference('split', [status(esa)], ['30'])).
% 5.55/5.74  thf('32', plain,
% 5.55/5.74      (((r1_tsep_1 @ sk_C @ sk_D)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_D)
% 5.55/5.74        | ~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('33', plain,
% 5.55/5.74      (((r1_tsep_1 @ sk_C @ sk_D)) | 
% 5.55/5.74       ~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 5.55/5.74       ((r1_tsep_1 @ sk_B @ sk_D))),
% 5.55/5.74      inference('split', [status(esa)], ['32'])).
% 5.55/5.74  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('37', plain,
% 5.55/5.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.55/5.74         ((v2_struct_0 @ X11)
% 5.55/5.74          | ~ (m1_pre_topc @ X11 @ X12)
% 5.55/5.74          | (r1_tsep_1 @ X11 @ X13)
% 5.55/5.74          | (m1_pre_topc @ (k2_tsep_1 @ X12 @ X11 @ X13) @ X11)
% 5.55/5.74          | ~ (m1_pre_topc @ X13 @ X12)
% 5.55/5.74          | (v2_struct_0 @ X13)
% 5.55/5.74          | ~ (l1_pre_topc @ X12)
% 5.55/5.74          | ~ (v2_pre_topc @ X12)
% 5.55/5.74          | (v2_struct_0 @ X12))),
% 5.55/5.74      inference('cnf', [status(esa)], [t30_tsep_1])).
% 5.55/5.74  thf('38', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | ~ (v2_pre_topc @ sk_A)
% 5.55/5.74          | ~ (l1_pre_topc @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_B))),
% 5.55/5.74      inference('sup-', [status(thm)], ['36', '37'])).
% 5.55/5.74  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('41', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_B))),
% 5.55/5.74      inference('demod', [status(thm)], ['38', '39', '40'])).
% 5.55/5.74  thf('42', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_B)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_A))),
% 5.55/5.74      inference('sup-', [status(thm)], ['35', '41'])).
% 5.55/5.74  thf('43', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i]:
% 5.55/5.74         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 5.55/5.74          | (zip_tseitin_0 @ X1 @ X0)
% 5.55/5.74          | (zip_tseitin_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_C))),
% 5.55/5.74      inference('simplify', [status(thm)], ['21'])).
% 5.55/5.74  thf('44', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 5.55/5.74          | (zip_tseitin_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (zip_tseitin_0 @ X0 @ sk_B)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['42', '43'])).
% 5.55/5.74  thf('45', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('46', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (zip_tseitin_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (zip_tseitin_0 @ X0 @ sk_B)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('demod', [status(thm)], ['44', '45'])).
% 5.55/5.74  thf('47', plain,
% 5.55/5.74      (![X0 : $i]:
% 5.55/5.74         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.55/5.74          | (zip_tseitin_0 @ X0 @ sk_B)
% 5.55/5.74          | (zip_tseitin_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74          | (v2_struct_0 @ sk_B)
% 5.55/5.74          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_C)
% 5.55/5.74          | (v2_struct_0 @ sk_A))),
% 5.55/5.74      inference('simplify', [status(thm)], ['46'])).
% 5.55/5.74  thf('48', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_A)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (zip_tseitin_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['34', '47'])).
% 5.55/5.74  thf('49', plain,
% 5.55/5.74      (![X5 : $i, X6 : $i]:
% 5.55/5.74         ((r1_tsep_1 @ X6 @ X5) | ~ (zip_tseitin_1 @ X6 @ X5))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.55/5.74  thf('50', plain,
% 5.55/5.74      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_A)
% 5.55/5.74        | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['48', '49'])).
% 5.55/5.74  thf('51', plain,
% 5.55/5.74      ((~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.74      inference('split', [status(esa)], ['30'])).
% 5.55/5.74  thf('52', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_D)
% 5.55/5.74         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.74      inference('sup-', [status(thm)], ['50', '51'])).
% 5.55/5.74  thf('53', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.74         (~ (m1_pre_topc @ X0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (l1_pre_topc @ X1)
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X2)
% 5.55/5.74          | ~ (m1_pre_topc @ X2 @ X1)
% 5.55/5.74          | ~ (v2_struct_0 @ (k2_tsep_1 @ X1 @ X0 @ X2)))),
% 5.55/5.74      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 5.55/5.74  thf('54', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | ~ (l1_pre_topc @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.74      inference('sup-', [status(thm)], ['52', '53'])).
% 5.55/5.74  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('58', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_B)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.74      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 5.55/5.74  thf('59', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_D)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.74      inference('simplify', [status(thm)], ['58'])).
% 5.55/5.74  thf('60', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('61', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.74      inference('sup-', [status(thm)], ['59', '60'])).
% 5.55/5.74  thf('62', plain,
% 5.55/5.74      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('split', [status(esa)], ['32'])).
% 5.55/5.74  thf('63', plain,
% 5.55/5.74      (![X3 : $i, X4 : $i]:
% 5.55/5.74         (~ (r1_tsep_1 @ X3 @ X4) | ~ (zip_tseitin_0 @ X4 @ X3))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.55/5.74  thf('64', plain,
% 5.55/5.74      ((~ (zip_tseitin_0 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['62', '63'])).
% 5.55/5.74  thf('65', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_D)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['61', '64'])).
% 5.55/5.74  thf('66', plain, (~ (v2_struct_0 @ sk_D)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('67', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['65', '66'])).
% 5.55/5.74  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('69', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('clc', [status(thm)], ['67', '68'])).
% 5.55/5.74  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('71', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_C))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('clc', [status(thm)], ['69', '70'])).
% 5.55/5.74  thf('72', plain, (~ (v2_struct_0 @ sk_C)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('73', plain,
% 5.55/5.74      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 5.55/5.74       ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['71', '72'])).
% 5.55/5.74  thf('74', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_A)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (zip_tseitin_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['34', '47'])).
% 5.55/5.74  thf('75', plain,
% 5.55/5.74      (![X5 : $i, X6 : $i]:
% 5.55/5.74         ((r1_tsep_1 @ X5 @ X6) | ~ (zip_tseitin_1 @ X6 @ X5))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.55/5.74  thf('76', plain,
% 5.55/5.74      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_A)
% 5.55/5.74        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 5.55/5.74      inference('sup-', [status(thm)], ['74', '75'])).
% 5.55/5.74  thf('77', plain,
% 5.55/5.74      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('split', [status(esa)], ['30'])).
% 5.55/5.74  thf('78', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_D)
% 5.55/5.74         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['76', '77'])).
% 5.55/5.74  thf('79', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.74         (~ (m1_pre_topc @ X0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (l1_pre_topc @ X1)
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X2)
% 5.55/5.74          | ~ (m1_pre_topc @ X2 @ X1)
% 5.55/5.74          | ~ (v2_struct_0 @ (k2_tsep_1 @ X1 @ X0 @ X2)))),
% 5.55/5.74      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 5.55/5.74  thf('80', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | ~ (l1_pre_topc @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['78', '79'])).
% 5.55/5.74  thf('81', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('83', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('84', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_B)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 5.55/5.74  thf('85', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_D)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('simplify', [status(thm)], ['84'])).
% 5.55/5.74  thf('86', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('87', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['85', '86'])).
% 5.55/5.74  thf('88', plain,
% 5.55/5.74      ((~ (zip_tseitin_0 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['62', '63'])).
% 5.55/5.74  thf('89', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_D)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['87', '88'])).
% 5.55/5.74  thf('90', plain, (~ (v2_struct_0 @ sk_D)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('91', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['89', '90'])).
% 5.55/5.74  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('93', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('clc', [status(thm)], ['91', '92'])).
% 5.55/5.74  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('95', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_C))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 5.55/5.74      inference('clc', [status(thm)], ['93', '94'])).
% 5.55/5.74  thf('96', plain, (~ (v2_struct_0 @ sk_C)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('97', plain,
% 5.55/5.74      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 5.55/5.74       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 5.55/5.74      inference('sup-', [status(thm)], ['95', '96'])).
% 5.55/5.74  thf('98', plain,
% 5.55/5.74      (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 5.55/5.74       ~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 5.55/5.74      inference('split', [status(esa)], ['30'])).
% 5.55/5.74  thf('99', plain,
% 5.55/5.74      (((v2_struct_0 @ sk_A)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (zip_tseitin_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['1', '26'])).
% 5.55/5.74  thf('100', plain,
% 5.55/5.74      (![X5 : $i, X6 : $i]:
% 5.55/5.74         ((r1_tsep_1 @ X5 @ X6) | ~ (zip_tseitin_1 @ X6 @ X5))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.55/5.74  thf('101', plain,
% 5.55/5.74      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 5.55/5.74        | (v2_struct_0 @ sk_D)
% 5.55/5.74        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_B)
% 5.55/5.74        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_C)
% 5.55/5.74        | (v2_struct_0 @ sk_A)
% 5.55/5.74        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 5.55/5.74      inference('sup-', [status(thm)], ['99', '100'])).
% 5.55/5.74  thf('102', plain,
% 5.55/5.74      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('split', [status(esa)], ['30'])).
% 5.55/5.74  thf('103', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_D)
% 5.55/5.74         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['101', '102'])).
% 5.55/5.74  thf('104', plain,
% 5.55/5.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.74         (~ (m1_pre_topc @ X0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X0)
% 5.55/5.74          | ~ (l1_pre_topc @ X1)
% 5.55/5.74          | (v2_struct_0 @ X1)
% 5.55/5.74          | (v2_struct_0 @ X2)
% 5.55/5.74          | ~ (m1_pre_topc @ X2 @ X1)
% 5.55/5.74          | ~ (v2_struct_0 @ (k2_tsep_1 @ X1 @ X0 @ X2)))),
% 5.55/5.74      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 5.55/5.74  thf('105', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | ~ (l1_pre_topc @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['103', '104'])).
% 5.55/5.74  thf('106', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('108', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('109', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_B)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 5.55/5.74  thf('110', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_D)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('simplify', [status(thm)], ['109'])).
% 5.55/5.74  thf('111', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.74  thf('112', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_D)
% 5.55/5.74         | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_A)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['110', '111'])).
% 5.55/5.74  thf('113', plain,
% 5.55/5.74      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.74      inference('split', [status(esa)], ['32'])).
% 5.55/5.74  thf('114', plain,
% 5.55/5.74      (![X3 : $i, X4 : $i]:
% 5.55/5.74         (~ (r1_tsep_1 @ X3 @ X4) | ~ (zip_tseitin_0 @ X4 @ X3))),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.55/5.74  thf('115', plain,
% 5.55/5.74      ((~ (zip_tseitin_0 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['113', '114'])).
% 5.55/5.74  thf('116', plain,
% 5.55/5.74      ((((v2_struct_0 @ sk_A)
% 5.55/5.74         | (v2_struct_0 @ sk_C)
% 5.55/5.74         | (v2_struct_0 @ sk_B)
% 5.55/5.74         | (v2_struct_0 @ sk_D)))
% 5.55/5.74         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.74             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.74      inference('sup-', [status(thm)], ['112', '115'])).
% 5.55/5.74  thf('117', plain, (~ (v2_struct_0 @ sk_D)),
% 5.55/5.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('118', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.75             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['116', '117'])).
% 5.55/5.75  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('120', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.75             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('clc', [status(thm)], ['118', '119'])).
% 5.55/5.75  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('122', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_C))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 5.55/5.75             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('clc', [status(thm)], ['120', '121'])).
% 5.55/5.75  thf('123', plain, (~ (v2_struct_0 @ sk_C)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('124', plain,
% 5.55/5.75      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 5.55/5.75       ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 5.55/5.75      inference('sup-', [status(thm)], ['122', '123'])).
% 5.55/5.75  thf('125', plain,
% 5.55/5.75      (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.75      inference('sat_resolution*', [status(thm)],
% 5.55/5.75                ['33', '73', '97', '98', '124'])).
% 5.55/5.75  thf('126', plain, (~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 5.55/5.75      inference('simpl_trail', [status(thm)], ['31', '125'])).
% 5.55/5.75  thf('127', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_A)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_D)
% 5.55/5.75        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['29', '126'])).
% 5.55/5.75  thf('128', plain,
% 5.55/5.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.75         (~ (m1_pre_topc @ X0 @ X1)
% 5.55/5.75          | (v2_struct_0 @ X0)
% 5.55/5.75          | ~ (l1_pre_topc @ X1)
% 5.55/5.75          | (v2_struct_0 @ X1)
% 5.55/5.75          | (v2_struct_0 @ X2)
% 5.55/5.75          | ~ (m1_pre_topc @ X2 @ X1)
% 5.55/5.75          | ~ (v2_struct_0 @ (k2_tsep_1 @ X1 @ X0 @ X2)))),
% 5.55/5.75      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 5.55/5.75  thf('129', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_D)
% 5.55/5.75        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_A)
% 5.55/5.75        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_A)
% 5.55/5.75        | ~ (l1_pre_topc @ sk_A)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 5.55/5.75      inference('sup-', [status(thm)], ['127', '128'])).
% 5.55/5.75  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('132', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('133', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_D)
% 5.55/5.75        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_A)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_A)
% 5.55/5.75        | (v2_struct_0 @ sk_B))),
% 5.55/5.75      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 5.55/5.75  thf('134', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_A)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_D))),
% 5.55/5.75      inference('simplify', [status(thm)], ['133'])).
% 5.55/5.75  thf('135', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('136', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_D)
% 5.55/5.75        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_A))),
% 5.55/5.75      inference('sup-', [status(thm)], ['134', '135'])).
% 5.55/5.75  thf('137', plain,
% 5.55/5.75      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 5.55/5.75        | (r1_tsep_1 @ sk_D @ sk_B)
% 5.55/5.75        | (r1_tsep_1 @ sk_D @ sk_C))),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('138', plain,
% 5.55/5.75      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 5.55/5.75      inference('split', [status(esa)], ['137'])).
% 5.55/5.75  thf('139', plain,
% 5.55/5.75      (![X3 : $i, X4 : $i]:
% 5.55/5.75         (~ (r1_tsep_1 @ X4 @ X3) | ~ (zip_tseitin_0 @ X4 @ X3))),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.55/5.75  thf('140', plain,
% 5.55/5.75      ((~ (zip_tseitin_0 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['138', '139'])).
% 5.55/5.75  thf('141', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_A)
% 5.55/5.75         | (v2_struct_0 @ sk_C)
% 5.55/5.75         | (v2_struct_0 @ sk_B)
% 5.55/5.75         | (v2_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['136', '140'])).
% 5.55/5.75  thf('142', plain,
% 5.55/5.75      (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 5.55/5.75       ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 5.55/5.75      inference('split', [status(esa)], ['32'])).
% 5.55/5.75  thf('143', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_D)
% 5.55/5.75         | (zip_tseitin_0 @ sk_D @ sk_B)
% 5.55/5.75         | (v2_struct_0 @ sk_B)
% 5.55/5.75         | (v2_struct_0 @ sk_C)
% 5.55/5.75         | (v2_struct_0 @ sk_A)))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 5.55/5.75      inference('sup-', [status(thm)], ['59', '60'])).
% 5.55/5.75  thf('144', plain,
% 5.55/5.75      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 5.55/5.75      inference('split', [status(esa)], ['137'])).
% 5.55/5.75  thf('145', plain,
% 5.55/5.75      (![X3 : $i, X4 : $i]:
% 5.55/5.75         (~ (r1_tsep_1 @ X4 @ X3) | ~ (zip_tseitin_0 @ X4 @ X3))),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.55/5.75  thf('146', plain,
% 5.55/5.75      ((~ (zip_tseitin_0 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['144', '145'])).
% 5.55/5.75  thf('147', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_A)
% 5.55/5.75         | (v2_struct_0 @ sk_C)
% 5.55/5.75         | (v2_struct_0 @ sk_B)
% 5.55/5.75         | (v2_struct_0 @ sk_D)))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.75             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['143', '146'])).
% 5.55/5.75  thf('148', plain, (~ (v2_struct_0 @ sk_D)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('149', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.75             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['147', '148'])).
% 5.55/5.75  thf('150', plain, (~ (v2_struct_0 @ sk_B)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('151', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.75             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 5.55/5.75      inference('clc', [status(thm)], ['149', '150'])).
% 5.55/5.75  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('153', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_C))
% 5.55/5.75         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 5.55/5.75             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 5.55/5.75      inference('clc', [status(thm)], ['151', '152'])).
% 5.55/5.75  thf('154', plain, (~ (v2_struct_0 @ sk_C)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('155', plain,
% 5.55/5.75      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | 
% 5.55/5.75       ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['153', '154'])).
% 5.55/5.75  thf('156', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_D)
% 5.55/5.75        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_A))),
% 5.55/5.75      inference('sup-', [status(thm)], ['134', '135'])).
% 5.55/5.75  thf('157', plain,
% 5.55/5.75      ((~ (zip_tseitin_0 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['113', '114'])).
% 5.55/5.75  thf('158', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_A)
% 5.55/5.75         | (v2_struct_0 @ sk_C)
% 5.55/5.75         | (v2_struct_0 @ sk_B)
% 5.55/5.75         | (v2_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['156', '157'])).
% 5.55/5.75  thf('159', plain, (~ (v2_struct_0 @ sk_D)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('160', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 5.55/5.75         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('sup-', [status(thm)], ['158', '159'])).
% 5.55/5.75  thf('161', plain, (~ (v2_struct_0 @ sk_B)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('162', plain,
% 5.55/5.75      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 5.55/5.75         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('clc', [status(thm)], ['160', '161'])).
% 5.55/5.75  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('164', plain, (((v2_struct_0 @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 5.55/5.75      inference('clc', [status(thm)], ['162', '163'])).
% 5.55/5.75  thf('165', plain, (~ (v2_struct_0 @ sk_C)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('166', plain, (~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 5.55/5.75      inference('sup-', [status(thm)], ['164', '165'])).
% 5.55/5.75  thf('167', plain,
% 5.55/5.75      (((r1_tsep_1 @ sk_C @ sk_D)
% 5.55/5.75        | (r1_tsep_1 @ sk_B @ sk_D)
% 5.55/5.75        | (r1_tsep_1 @ sk_D @ sk_B)
% 5.55/5.75        | (r1_tsep_1 @ sk_D @ sk_C))),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('168', plain,
% 5.55/5.75      (((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 5.55/5.75       ((r1_tsep_1 @ sk_B @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 5.55/5.75      inference('split', [status(esa)], ['167'])).
% 5.55/5.75  thf('169', plain, (((r1_tsep_1 @ sk_D @ sk_C))),
% 5.55/5.75      inference('sat_resolution*', [status(thm)],
% 5.55/5.75                ['142', '124', '155', '73', '97', '98', '166', '168'])).
% 5.55/5.75  thf('170', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_A)
% 5.55/5.75        | (v2_struct_0 @ sk_C)
% 5.55/5.75        | (v2_struct_0 @ sk_B)
% 5.55/5.75        | (v2_struct_0 @ sk_D))),
% 5.55/5.75      inference('simpl_trail', [status(thm)], ['141', '169'])).
% 5.55/5.75  thf('171', plain, (~ (v2_struct_0 @ sk_D)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('172', plain,
% 5.55/5.75      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 5.55/5.75      inference('sup-', [status(thm)], ['170', '171'])).
% 5.55/5.75  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('174', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 5.55/5.75      inference('clc', [status(thm)], ['172', '173'])).
% 5.55/5.75  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 5.55/5.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.75  thf('176', plain, ((v2_struct_0 @ sk_C)),
% 5.55/5.75      inference('clc', [status(thm)], ['174', '175'])).
% 5.55/5.75  thf('177', plain, ($false), inference('demod', [status(thm)], ['0', '176'])).
% 5.55/5.75  
% 5.55/5.75  % SZS output end Refutation
% 5.55/5.75  
% 5.55/5.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
