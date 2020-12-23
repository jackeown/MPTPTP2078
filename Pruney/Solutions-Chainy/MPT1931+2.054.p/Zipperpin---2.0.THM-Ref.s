%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cvmTRhREka

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:04 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 135 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  775 (1397 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('10',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ( r1_waybel_0 @ X26 @ X25 @ ( k6_subset_1 @ ( u1_struct_0 @ X26 ) @ X27 ) )
      | ( r2_waybel_0 @ X26 @ X25 @ X27 )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ( r1_waybel_0 @ X26 @ X25 @ ( k4_xboole_0 @ ( u1_struct_0 @ X26 ) @ X27 ) )
      | ( r2_waybel_0 @ X26 @ X25 @ X27 )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( m1_subset_1 @ ( sk_D @ X21 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ( r2_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r2_waybel_0 @ X20 @ X19 @ X23 )
      | ( r2_hidden @ ( k2_waybel_0 @ X20 @ X19 @ ( sk_E @ X24 @ X23 @ X19 @ X20 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('46',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('47',plain,(
    ! [X19: $i,X20: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r2_waybel_0 @ X20 @ X19 @ X23 )
      | ( r2_hidden @ ( k2_waybel_0 @ X20 @ X19 @ ( sk_E @ X24 @ X23 @ X19 @ X20 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ X0 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['2','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cvmTRhREka
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 80 iterations in 0.062s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.33/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.33/0.52  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.33/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.33/0.52  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.33/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.33/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.33/0.52  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.33/0.52  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.33/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.33/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.33/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.33/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.33/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.52  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.33/0.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(t4_subset_1, axiom,
% 0.33/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.33/0.52  thf('0', plain,
% 0.33/0.52      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.33/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.33/0.52  thf(t3_subset, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.33/0.52  thf('1', plain,
% 0.33/0.52      (![X11 : $i, X12 : $i]:
% 0.33/0.52         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.33/0.52  thf('2', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.33/0.52  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.33/0.52  thf(t3_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.33/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.33/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.33/0.52  thf('4', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf(t7_ordinal1, axiom,
% 0.33/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.33/0.52  thf('5', plain,
% 0.33/0.52      (![X17 : $i, X18 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.33/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.33/0.52  thf('6', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.33/0.52  thf('7', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['3', '6'])).
% 0.33/0.52  thf(t83_xboole_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.33/0.52  thf('8', plain,
% 0.33/0.52      (![X4 : $i, X5 : $i]:
% 0.33/0.52         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.33/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.33/0.52  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.33/0.52  thf(t29_yellow_6, conjecture,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.33/0.52             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.33/0.52           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i]:
% 0.33/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.33/0.52          ( ![B:$i]:
% 0.33/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.33/0.52                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.33/0.52              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.33/0.52  thf('10', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(t10_waybel_0, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.33/0.52               ( ~( r1_waybel_0 @
% 0.33/0.52                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.33/0.52         ((v2_struct_0 @ X25)
% 0.33/0.52          | ~ (l1_waybel_0 @ X25 @ X26)
% 0.33/0.52          | (r1_waybel_0 @ X26 @ X25 @ 
% 0.33/0.52             (k6_subset_1 @ (u1_struct_0 @ X26) @ X27))
% 0.33/0.52          | (r2_waybel_0 @ X26 @ X25 @ X27)
% 0.33/0.52          | ~ (l1_struct_0 @ X26)
% 0.33/0.52          | (v2_struct_0 @ X26))),
% 0.33/0.52      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.33/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.33/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.33/0.52  thf('13', plain,
% 0.33/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.33/0.52         ((v2_struct_0 @ X25)
% 0.33/0.52          | ~ (l1_waybel_0 @ X25 @ X26)
% 0.33/0.52          | (r1_waybel_0 @ X26 @ X25 @ 
% 0.33/0.52             (k4_xboole_0 @ (u1_struct_0 @ X26) @ X27))
% 0.33/0.52          | (r2_waybel_0 @ X26 @ X25 @ X27)
% 0.33/0.52          | ~ (l1_struct_0 @ X26)
% 0.33/0.52          | (v2_struct_0 @ X26))),
% 0.33/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.33/0.52  thf('14', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_A)
% 0.33/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['10', '13'])).
% 0.33/0.52  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('16', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.33/0.52  thf('17', plain,
% 0.33/0.52      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.33/0.52        | (v2_struct_0 @ sk_B_1)
% 0.33/0.52        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.33/0.52        | (v2_struct_0 @ sk_A))),
% 0.33/0.52      inference('sup+', [status(thm)], ['9', '16'])).
% 0.33/0.52  thf('18', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('19', plain,
% 0.33/0.52      (((v2_struct_0 @ sk_A)
% 0.33/0.52        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.33/0.52        | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.33/0.52  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('21', plain,
% 0.33/0.52      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.33/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.33/0.52  thf('22', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('23', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.33/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.33/0.52  thf('24', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('25', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(d12_waybel_0, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.33/0.52               ( ![D:$i]:
% 0.33/0.52                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.33/0.52                   ( ?[E:$i]:
% 0.33/0.52                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.33/0.52                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.33/0.52                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.52  thf('26', plain,
% 0.33/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.33/0.52         ((v2_struct_0 @ X19)
% 0.33/0.52          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.33/0.52          | (m1_subset_1 @ (sk_D @ X21 @ X19 @ X20) @ (u1_struct_0 @ X19))
% 0.33/0.52          | (r2_waybel_0 @ X20 @ X19 @ X21)
% 0.33/0.52          | ~ (l1_struct_0 @ X20)
% 0.33/0.52          | (v2_struct_0 @ X20))),
% 0.33/0.52      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.33/0.52  thf('27', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_A)
% 0.33/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.33/0.52  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('29', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.33/0.52  thf('30', plain,
% 0.33/0.52      (![X19 : $i, X20 : $i, X23 : $i, X24 : $i]:
% 0.33/0.52         ((v2_struct_0 @ X19)
% 0.33/0.52          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.33/0.52          | ~ (r2_waybel_0 @ X20 @ X19 @ X23)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ X20 @ X19 @ (sk_E @ X24 @ X23 @ X19 @ X20)) @ X23)
% 0.33/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X19))
% 0.33/0.52          | ~ (l1_struct_0 @ X20)
% 0.33/0.52          | (v2_struct_0 @ X20))),
% 0.33/0.52      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.33/0.52  thf('31', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_B_1)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | (v2_struct_0 @ X1)
% 0.33/0.52          | ~ (l1_struct_0 @ X1)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.33/0.52             X2)
% 0.33/0.52          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.33/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.33/0.52  thf('32', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.33/0.52          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.33/0.52             X2)
% 0.33/0.52          | ~ (l1_struct_0 @ X1)
% 0.33/0.52          | (v2_struct_0 @ X1)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.33/0.52  thf('33', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_B_1)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52             X1)
% 0.33/0.52          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['24', '32'])).
% 0.33/0.52  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('35', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_B_1)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52             X1)
% 0.33/0.52          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.33/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.33/0.52  thf('36', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52             X1)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.33/0.52  thf('37', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_B_1)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52             k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['23', '36'])).
% 0.33/0.52  thf('38', plain,
% 0.33/0.52      (![X17 : $i, X18 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.33/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.33/0.52  thf('39', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_B_1)
% 0.33/0.52          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.33/0.52               (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52                (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0 @ sk_B_1 @ 
% 0.33/0.52                 sk_A))))),
% 0.33/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.33/0.52  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.33/0.52  thf('41', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.33/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.33/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.33/0.52  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('43', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.33/0.52      inference('clc', [status(thm)], ['41', '42'])).
% 0.33/0.52  thf('44', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('45', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.33/0.52      inference('clc', [status(thm)], ['43', '44'])).
% 0.33/0.52  thf(existence_m1_subset_1, axiom,
% 0.33/0.52    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.33/0.52  thf('46', plain, (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.33/0.52      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.33/0.52  thf('47', plain,
% 0.33/0.52      (![X19 : $i, X20 : $i, X23 : $i, X24 : $i]:
% 0.33/0.52         ((v2_struct_0 @ X19)
% 0.33/0.52          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.33/0.52          | ~ (r2_waybel_0 @ X20 @ X19 @ X23)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ X20 @ X19 @ (sk_E @ X24 @ X23 @ X19 @ X20)) @ X23)
% 0.33/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X19))
% 0.33/0.52          | ~ (l1_struct_0 @ X20)
% 0.33/0.52          | (v2_struct_0 @ X20))),
% 0.33/0.52      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.33/0.52  thf('48', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         ((v2_struct_0 @ X1)
% 0.33/0.52          | ~ (l1_struct_0 @ X1)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ X1 @ X0 @ 
% 0.33/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.33/0.52             X2)
% 0.33/0.52          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.33/0.52          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.33/0.52          | (v2_struct_0 @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.33/0.52  thf('49', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_B_1)
% 0.33/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.33/0.52          | (v2_struct_0 @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['45', '48'])).
% 0.33/0.52  thf('50', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('52', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_B_1)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | (v2_struct_0 @ sk_A))),
% 0.33/0.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.33/0.52  thf('53', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('54', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v2_struct_0 @ sk_A)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52             X0))),
% 0.33/0.52      inference('clc', [status(thm)], ['52', '53'])).
% 0.33/0.52  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('56', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (r2_hidden @ 
% 0.33/0.52          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.33/0.52          X0)),
% 0.33/0.52      inference('clc', [status(thm)], ['54', '55'])).
% 0.33/0.52  thf('57', plain,
% 0.33/0.52      (![X17 : $i, X18 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.33/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.33/0.52  thf('58', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ~ (r1_tarski @ X0 @ 
% 0.33/0.52            (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.33/0.52             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.33/0.52  thf('59', plain, ($false), inference('sup-', [status(thm)], ['2', '58'])).
% 0.33/0.52  
% 0.33/0.52  % SZS output end Refutation
% 0.33/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
