%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J82Fs2WBf3

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:52 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 449 expanded)
%              Number of leaves         :   30 ( 133 expanded)
%              Depth                    :   29
%              Number of atoms          : 2425 (8492 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t8_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( r1_tarski @ C @ D )
             => ( ( ( r1_waybel_0 @ A @ B @ C )
                 => ( r1_waybel_0 @ A @ B @ D ) )
                & ( ( r2_waybel_0 @ A @ B @ C )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i,D: $i] :
                ( ( r1_tarski @ C @ D )
               => ( ( ( r1_waybel_0 @ A @ B @ C )
                   => ( r1_waybel_0 @ A @ B @ D ) )
                  & ( ( r2_waybel_0 @ A @ B @ C )
                   => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_0])).

thf('0',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_waybel_0 @ X7 @ X6 @ X10 )
      | ( r2_hidden @ ( k2_waybel_0 @ X7 @ X6 @ ( sk_E_1 @ X11 @ X10 @ X6 @ X7 ) ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_C @ sk_B_1 @ sk_A ) ) @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_C @ sk_B_1 @ sk_A ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_C @ sk_B_1 @ sk_A ) ) @ sk_C ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_C @ sk_B_1 @ sk_A ) ) @ sk_C )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('20',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_D_1 @ X8 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ( r2_waybel_0 @ X7 @ X6 @ X8 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_waybel_0 @ X7 @ X6 @ X10 )
      | ( r2_hidden @ ( k2_waybel_0 @ X7 @ X6 @ ( sk_E_1 @ X11 @ X10 @ X6 @ X7 ) ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ sk_C ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    r1_tarski @ sk_C @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('43',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_waybel_0 @ X7 @ X6 @ X10 )
      | ( r1_orders_2 @ X6 @ X11 @ ( sk_E_1 @ X11 @ X10 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('54',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_waybel_0 @ X7 @ X6 @ X10 )
      | ( m1_subset_1 @ ( sk_E_1 @ X11 @ X10 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_orders_2 @ X6 @ ( sk_D_1 @ X8 @ X6 @ X7 ) @ X9 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X7 @ X6 @ X9 ) @ X8 )
      | ( r2_waybel_0 @ X7 @ X6 @ X8 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('65',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( l1_struct_0 @ X1 )
        | ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
        | ~ ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ X2 )
        | ~ ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X2 @ sk_B_1 @ X1 ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
        | ~ ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X2 @ sk_B_1 @ X1 ) @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ X2 )
        | ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
        | ~ ( l1_struct_0 @ X1 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ X0 )
        | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ X0 ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_C @ sk_B_1 @ sk_A ) ) @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','71'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 ) )
   <= ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
   <= ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_D_2 ) )
   <= ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
   <= ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('81',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','83'])).

thf('85',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('86',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf(d11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ? [D: $i] :
                  ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( r1_orders_2 @ B @ D @ E )
                       => ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) )
                  & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('98',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( r1_waybel_0 @ X0 @ sk_B_1 @ X1 )
        | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( l1_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('105',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( r1_waybel_0 @ X0 @ sk_B_1 @ X1 )
        | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ X0 ) )
        | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( l1_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_D @ X4 @ X0 @ X1 ) @ X5 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_C )
        | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
        | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('113',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_C )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_C )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( v2_struct_0 @ sk_B_1 )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_C ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_C )
        | ( v2_struct_0 @ sk_B_1 )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_C )
        | ( v2_struct_0 @ sk_B_1 )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 )
        | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('127',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 ) )
   <= ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
   <= ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('131',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_D_2 ) )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('137',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 ) )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ! [X0: $i] :
        ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
   <= ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
   <= ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('144',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','84','85','144'])).


%------------------------------------------------------------------------------
