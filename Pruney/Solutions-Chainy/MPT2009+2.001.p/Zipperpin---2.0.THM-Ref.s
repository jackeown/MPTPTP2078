%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TLLXsYTmUL

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:19 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 312 expanded)
%              Number of leaves         :   43 ( 105 expanded)
%              Depth                    :   32
%              Number of atoms          : 1889 (4564 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(o_2_4_waybel_9_type,type,(
    o_2_4_waybel_9: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t8_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_9])).

thf('1',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_o_2_4_waybel_9,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( o_2_4_waybel_9 @ A @ B ) @ ( u1_struct_0 @ B ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X33 )
      | ( m1_subset_1 @ ( o_2_4_waybel_9 @ X33 @ X34 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_4_waybel_9])).

thf('5',plain,
    ( ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_E @ X10 @ X11 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ sk_B_2 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X1 @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( l1_waybel_0 @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( ( k2_waybel_0 @ X21 @ X20 @ X22 )
        = ( k3_funct_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d8_waybel_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B_2 ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B_2 ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_waybel_0 @ X26 @ X25 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t189_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X3 ) ) )
      | ( r2_hidden @ ( k3_funct_2 @ X5 @ X3 @ X4 @ X6 ) @ ( k2_relset_1 @ X5 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t189_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_waybel_0 @ X26 @ X25 )
      | ( v1_funct_2 @ ( u1_waybel_0 @ X25 @ X26 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('34',plain,
    ( ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_waybel_0 @ X26 @ X25 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('39',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X9 @ X8 @ ( sk_E @ X10 @ X11 @ X8 @ X9 ) ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
    | ~ ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('50',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(rc5_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ? [B: $i] :
          ( ( v7_waybel_0 @ B )
          & ( v6_waybel_0 @ B @ A )
          & ( v5_orders_2 @ B )
          & ( v4_orders_2 @ B )
          & ( v3_orders_2 @ B )
          & ~ ( v2_struct_0 @ B )
          & ( l1_waybel_0 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X27: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X27 ) @ X27 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('57',plain,(
    ! [X27: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('58',plain,(
    ! [X27: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('59',plain,(
    ! [X27: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('60',plain,(
    ! [X27: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X27 ) @ X27 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf(t29_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf('61',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ( r1_waybel_0 @ X32 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow_6])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( r1_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( r1_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( r1_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(t28_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
             => ( r2_waybel_0 @ A @ B @ C ) ) ) ) )).

thf('68',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ( r2_waybel_0 @ X29 @ X28 @ X30 )
      | ~ ( r1_waybel_0 @ X29 @ X28 @ X30 )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow_6])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X0 )
      | ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X0 )
      | ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X0 )
      | ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X27: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X27 ) @ X27 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('78',plain,(
    ! [X27: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X27 ) @ X27 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('79',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X33 )
      | ( m1_subset_1 @ ( o_2_4_waybel_9 @ X33 @ X34 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_4_waybel_9])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( sk_B_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( sk_B_1 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

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

thf('82',plain,(
    ! [X14: $i,X15: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( r2_waybel_0 @ X15 @ X14 @ X18 )
      | ( r2_hidden @ ( k2_waybel_0 @ X15 @ X14 @ ( sk_E_1 @ X19 @ X18 @ X14 @ X15 ) ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ ( sk_B_1 @ X0 ) @ ( sk_E_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ X2 @ ( sk_B_1 @ X0 ) @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ ( sk_B_1 @ X0 ) @ X2 )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ ( sk_B_1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ ( sk_B_1 @ X0 ) @ ( sk_E_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ X2 @ ( sk_B_1 @ X0 ) @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( sk_E_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ X1 @ ( sk_B_1 @ X0 ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( sk_E_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ X1 @ ( sk_B_1 @ X0 ) @ X0 ) ) @ X1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( sk_E_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( sk_B_1 @ X0 ) @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ X0 @ ( sk_B_1 @ X0 ) @ ( sk_E_1 @ ( o_2_4_waybel_9 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( sk_B_1 @ X0 ) @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X27: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B_1 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('104',plain,
    ( ( v2_struct_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X27: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B_1 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[rc5_waybel_0])).

thf('106',plain,
    ( ~ ( l1_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( l1_orders_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','108'])).

thf('110',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('111',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( l1_orders_2 @ X23 )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('112',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['109','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TLLXsYTmUL
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 136 iterations in 0.165s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.46/0.65  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.46/0.65  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.46/0.65  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.65  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.46/0.65  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.46/0.65  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.65  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.46/0.65  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.65  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(o_2_4_waybel_9_type, type, o_2_4_waybel_9: $i > $i > $i).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.46/0.65  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.46/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.65  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(dt_l1_orders_2, axiom,
% 0.46/0.65    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.65  thf('0', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.46/0.65  thf(t8_waybel_9, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65           ( r1_waybel_0 @
% 0.46/0.65             A @ B @ 
% 0.46/0.65             ( k2_relset_1 @
% 0.46/0.65               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.65               ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65              ( r1_waybel_0 @
% 0.46/0.65                A @ B @ 
% 0.46/0.65                ( k2_relset_1 @
% 0.46/0.65                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.65                  ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t8_waybel_9])).
% 0.46/0.65  thf('1', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('2', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('3', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_o_2_4_waybel_9, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.46/0.65         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65       ( m1_subset_1 @ ( o_2_4_waybel_9 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X33)
% 0.46/0.65          | (v2_struct_0 @ X33)
% 0.46/0.65          | (v2_struct_0 @ X34)
% 0.46/0.65          | ~ (l1_waybel_0 @ X34 @ X33)
% 0.46/0.65          | (m1_subset_1 @ (o_2_4_waybel_9 @ X33 @ X34) @ (u1_struct_0 @ X34)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_o_2_4_waybel_9])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ 
% 0.46/0.65         (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ 
% 0.46/0.65         (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf('8', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ 
% 0.46/0.65           (u1_struct_0 @ sk_B_2)))),
% 0.46/0.65      inference('clc', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      ((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf(d11_waybel_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.46/0.65               ( ?[D:$i]:
% 0.46/0.65                 ( ( ![E:$i]:
% 0.46/0.65                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.65                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.46/0.65                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.46/0.65                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X8)
% 0.46/0.65          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.46/0.65          | (m1_subset_1 @ (sk_E @ X10 @ X11 @ X8 @ X9) @ (u1_struct_0 @ X8))
% 0.46/0.65          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.46/0.65          | (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.46/0.65          | ~ (l1_struct_0 @ X9)
% 0.46/0.65          | (v2_struct_0 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (r1_waybel_0 @ X0 @ sk_B_2 @ X1)
% 0.46/0.65          | (m1_subset_1 @ 
% 0.46/0.65             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X1 @ sk_B_2 @ X0) @ 
% 0.46/0.65             (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | ~ (l1_waybel_0 @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (m1_subset_1 @ 
% 0.46/0.65             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.46/0.65             (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '13'])).
% 0.46/0.65  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (m1_subset_1 @ 
% 0.46/0.65             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.46/0.65             (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf(d8_waybel_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.65               ( ( k2_waybel_0 @ A @ B @ C ) =
% 0.46/0.65                 ( k3_funct_2 @
% 0.46/0.65                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.65                   ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X20)
% 0.46/0.65          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.46/0.65          | ((k2_waybel_0 @ X21 @ X20 @ X22)
% 0.46/0.65              = (k3_funct_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 0.46/0.65                 (u1_waybel_0 @ X21 @ X20) @ X22))
% 0.46/0.65          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.46/0.65          | ~ (l1_struct_0 @ X21)
% 0.46/0.65          | (v2_struct_0 @ X21))),
% 0.46/0.65      inference('cnf', [status(esa)], [d8_waybel_0])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X1)
% 0.46/0.65          | ~ (l1_struct_0 @ X1)
% 0.46/0.65          | ((k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.46/0.65              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A))
% 0.46/0.65              = (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ X1) @ 
% 0.46/0.65                 (u1_waybel_0 @ X1 @ sk_B_2) @ 
% 0.46/0.65                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A)))
% 0.46/0.65          | ~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.46/0.65          | ((k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.46/0.65              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A))
% 0.46/0.65              = (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ X1) @ 
% 0.46/0.65                 (u1_waybel_0 @ X1 @ sk_B_2) @ 
% 0.46/0.65                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A)))
% 0.46/0.65          | ~ (l1_struct_0 @ X1)
% 0.46/0.65          | (v2_struct_0 @ X1)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65          | ((k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A))
% 0.46/0.65              = (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65                 (u1_waybel_0 @ sk_A @ sk_B_2) @ 
% 0.46/0.65                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '19'])).
% 0.46/0.65  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ((k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A))
% 0.46/0.65              = (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65                 (u1_waybel_0 @ sk_A @ sk_B_2) @ 
% 0.46/0.65                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65            (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A))
% 0.46/0.65            = (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65               (u1_waybel_0 @ sk_A @ sk_B_2) @ 
% 0.46/0.65               (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A)))
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (m1_subset_1 @ 
% 0.46/0.65             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.46/0.65             (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('25', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_u1_waybel_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.46/0.65         ( v1_funct_2 @
% 0.46/0.65           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.65         ( m1_subset_1 @
% 0.46/0.65           ( u1_waybel_0 @ A @ B ) @ 
% 0.46/0.65           ( k1_zfmisc_1 @
% 0.46/0.65             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X25)
% 0.46/0.65          | ~ (l1_waybel_0 @ X26 @ X25)
% 0.46/0.65          | (m1_subset_1 @ (u1_waybel_0 @ X25 @ X26) @ 
% 0.46/0.65             (k1_zfmisc_1 @ 
% 0.46/0.65              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25)))))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_2) @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.65  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_2) @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf(t189_funct_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ A ) =>
% 0.46/0.65               ( ![D:$i]:
% 0.46/0.65                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.65                     ( m1_subset_1 @
% 0.46/0.65                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.65                   ( r2_hidden @
% 0.46/0.65                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.46/0.65                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X3)
% 0.46/0.65          | ~ (v1_funct_1 @ X4)
% 0.46/0.65          | ~ (v1_funct_2 @ X4 @ X5 @ X3)
% 0.46/0.65          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X3)))
% 0.46/0.65          | (r2_hidden @ (k3_funct_2 @ X5 @ X3 @ X4 @ X6) @ 
% 0.46/0.65             (k2_relset_1 @ X5 @ X3 @ X4))
% 0.46/0.65          | ~ (m1_subset_1 @ X6 @ X5)
% 0.46/0.65          | (v1_xboole_0 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [t189_funct_2])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65              (u1_waybel_0 @ sk_A @ sk_B_2) @ X0) @ 
% 0.46/0.65             (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65              (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65          | ~ (v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_2) @ 
% 0.46/0.65               (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('32', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X25)
% 0.46/0.65          | ~ (l1_waybel_0 @ X26 @ X25)
% 0.46/0.65          | (v1_funct_2 @ (u1_waybel_0 @ X25 @ X26) @ (u1_struct_0 @ X26) @ 
% 0.46/0.65             (u1_struct_0 @ X25)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_B_2) @ 
% 0.46/0.65         (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      ((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_B_2) @ 
% 0.46/0.65        (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('37', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X25)
% 0.46/0.65          | ~ (l1_waybel_0 @ X26 @ X25)
% 0.46/0.65          | (v1_funct_1 @ (u1_waybel_0 @ X25 @ X26)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_2)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('41', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_2))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65              (u1_waybel_0 @ sk_A @ sk_B_2) @ X0) @ 
% 0.46/0.65             (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65              (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['31', '36', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k3_funct_2 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65              (u1_waybel_0 @ sk_A @ sk_B_2) @ 
% 0.46/0.65              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.46/0.65             (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65              (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['24', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ 
% 0.46/0.65           (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65            (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.46/0.65           (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['23', '43'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65          | (v2_struct_0 @ sk_B_2)
% 0.46/0.65          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.46/0.65             (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65              (u1_waybel_0 @ sk_A @ sk_B_2))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X8)
% 0.46/0.65          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.46/0.65          | ~ (r2_hidden @ 
% 0.46/0.65               (k2_waybel_0 @ X9 @ X8 @ (sk_E @ X10 @ X11 @ X8 @ X9)) @ X11)
% 0.46/0.65          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.46/0.65          | (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.46/0.65          | ~ (l1_struct_0 @ X9)
% 0.46/0.65          | (v2_struct_0 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65           (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65           (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65        | ~ (m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ 
% 0.46/0.65             (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      ((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('50', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65           (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65           (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65           (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (u1_waybel_0 @ sk_A @ sk_B_2)))
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.46/0.65          (k2_relset_1 @ (u1_struct_0 @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65           (u1_waybel_0 @ sk_A @ sk_B_2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf(rc5_waybel_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) =>
% 0.46/0.65       ( ?[B:$i]:
% 0.46/0.65         ( ( v7_waybel_0 @ B ) & ( v6_waybel_0 @ B @ A ) & 
% 0.46/0.65           ( v5_orders_2 @ B ) & ( v4_orders_2 @ B ) & ( v3_orders_2 @ B ) & 
% 0.46/0.65           ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) ) ))).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X27 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (sk_B_1 @ X27) @ X27) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X27 : $i]: ((v7_waybel_0 @ (sk_B_1 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X27 : $i]: ((v4_orders_2 @ (sk_B_1 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X27 : $i]: ((v7_waybel_0 @ (sk_B_1 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X27 : $i]: ((v4_orders_2 @ (sk_B_1 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (![X27 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (sk_B_1 @ X27) @ X27) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf(t29_yellow_6, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.46/0.65             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (![X31 : $i, X32 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X31)
% 0.46/0.65          | ~ (v4_orders_2 @ X31)
% 0.46/0.65          | ~ (v7_waybel_0 @ X31)
% 0.46/0.65          | ~ (l1_waybel_0 @ X31 @ X32)
% 0.46/0.65          | (r1_waybel_0 @ X32 @ X31 @ (u1_struct_0 @ X32))
% 0.46/0.65          | ~ (l1_struct_0 @ X32)
% 0.46/0.65          | (v2_struct_0 @ X32))),
% 0.46/0.65      inference('cnf', [status(esa)], [t29_yellow_6])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (r1_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v7_waybel_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v4_orders_2 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v4_orders_2 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v7_waybel_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (r1_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (r1_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v7_waybel_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['59', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v7_waybel_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (r1_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (r1_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['58', '65'])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (r1_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.65  thf(t28_yellow_6, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.46/0.65             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( r1_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X28)
% 0.46/0.65          | ~ (v4_orders_2 @ X28)
% 0.46/0.65          | ~ (v7_waybel_0 @ X28)
% 0.46/0.65          | ~ (l1_waybel_0 @ X28 @ X29)
% 0.46/0.65          | (r2_waybel_0 @ X29 @ X28 @ X30)
% 0.46/0.65          | ~ (r1_waybel_0 @ X29 @ X28 @ X30)
% 0.46/0.65          | ~ (l1_struct_0 @ X29)
% 0.46/0.65          | (v2_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [t28_yellow_6])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X0)
% 0.46/0.65          | ~ (v7_waybel_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v4_orders_2 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v4_orders_2 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v7_waybel_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X0)
% 0.46/0.65          | (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X0)
% 0.46/0.65          | ~ (v7_waybel_0 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['57', '70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v7_waybel_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X0)
% 0.46/0.65          | (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['71'])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '72'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X0)
% 0.46/0.65          | (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['55', '74'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.65  thf('77', plain,
% 0.46/0.65      (![X27 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (sk_B_1 @ X27) @ X27) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X27 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (sk_B_1 @ X27) @ X27) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X33)
% 0.46/0.65          | (v2_struct_0 @ X33)
% 0.46/0.65          | (v2_struct_0 @ X34)
% 0.46/0.65          | ~ (l1_waybel_0 @ X34 @ X33)
% 0.46/0.65          | (m1_subset_1 @ (o_2_4_waybel_9 @ X33 @ X34) @ (u1_struct_0 @ X34)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_o_2_4_waybel_9])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | (m1_subset_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ 
% 0.46/0.65             (u1_struct_0 @ (sk_B_1 @ X0)))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (m1_subset_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ 
% 0.46/0.65             (u1_struct_0 @ (sk_B_1 @ X0)))
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['80'])).
% 0.46/0.65  thf(d12_waybel_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.46/0.65               ( ![D:$i]:
% 0.46/0.65                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.65                   ( ?[E:$i]:
% 0.46/0.65                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.46/0.65                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.46/0.65                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i, X18 : $i, X19 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X14)
% 0.46/0.65          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.46/0.65          | ~ (r2_waybel_0 @ X15 @ X14 @ X18)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k2_waybel_0 @ X15 @ X14 @ (sk_E_1 @ X19 @ X18 @ X14 @ X15)) @ X18)
% 0.46/0.65          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X14))
% 0.46/0.65          | ~ (l1_struct_0 @ X15)
% 0.46/0.65          | (v2_struct_0 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X1)
% 0.46/0.65          | ~ (l1_struct_0 @ X1)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k2_waybel_0 @ X1 @ (sk_B_1 @ X0) @ 
% 0.46/0.65              (sk_E_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ X2 @ 
% 0.46/0.65               (sk_B_1 @ X0) @ X1)) @ 
% 0.46/0.65             X2)
% 0.46/0.65          | ~ (r2_waybel_0 @ X1 @ (sk_B_1 @ X0) @ X2)
% 0.46/0.65          | ~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X1)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (l1_waybel_0 @ (sk_B_1 @ X0) @ X1)
% 0.46/0.65          | ~ (r2_waybel_0 @ X1 @ (sk_B_1 @ X0) @ X2)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k2_waybel_0 @ X1 @ (sk_B_1 @ X0) @ 
% 0.46/0.65              (sk_E_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ X2 @ 
% 0.46/0.65               (sk_B_1 @ X0) @ X1)) @ 
% 0.46/0.65             X2)
% 0.46/0.65          | ~ (l1_struct_0 @ X1)
% 0.46/0.65          | (v2_struct_0 @ X1)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['83'])).
% 0.46/0.65  thf('85', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ 
% 0.46/0.65              (sk_E_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ X1 @ 
% 0.46/0.65               (sk_B_1 @ X0) @ X0)) @ 
% 0.46/0.65             X1)
% 0.46/0.65          | ~ (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['77', '84'])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ X1)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ 
% 0.46/0.65              (sk_E_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ X1 @ 
% 0.46/0.65               (sk_B_1 @ X0) @ X0)) @ 
% 0.46/0.65             X1)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['85'])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (r2_hidden @ 
% 0.46/0.65             (k2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ 
% 0.46/0.65              (sk_E_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ 
% 0.46/0.65               (u1_struct_0 @ X0) @ (sk_B_1 @ X0) @ X0)) @ 
% 0.46/0.65             (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['76', '86'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ 
% 0.46/0.65           (k2_waybel_0 @ X0 @ (sk_B_1 @ X0) @ 
% 0.46/0.65            (sk_E_1 @ (o_2_4_waybel_9 @ X0 @ (sk_B_1 @ X0)) @ 
% 0.46/0.65             (u1_struct_0 @ X0) @ (sk_B_1 @ X0) @ X0)) @ 
% 0.46/0.65           (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['87'])).
% 0.46/0.65  thf(d1_xboole_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ (sk_B_1 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '90'])).
% 0.46/0.65  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ (sk_B_1 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      (((v2_struct_0 @ (sk_B_1 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['93'])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      (![X27 : $i]: (~ (v2_struct_0 @ (sk_B_1 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('96', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.65  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('98', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.65  thf('99', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('100', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.46/0.65      inference('clc', [status(thm)], ['98', '99'])).
% 0.46/0.65  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('102', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['100', '101'])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ (sk_B_1 @ X0))
% 0.46/0.65          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.65  thf('104', plain,
% 0.46/0.65      (((v2_struct_0 @ (sk_B_1 @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_B_2)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.65  thf('105', plain,
% 0.46/0.65      (![X27 : $i]: (~ (v2_struct_0 @ (sk_B_1 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc5_waybel_0])).
% 0.46/0.65  thf('106', plain, ((~ (l1_struct_0 @ sk_B_2) | (v2_struct_0 @ sk_B_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['104', '105'])).
% 0.46/0.65  thf('107', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('108', plain, (~ (l1_struct_0 @ sk_B_2)),
% 0.46/0.65      inference('clc', [status(thm)], ['106', '107'])).
% 0.46/0.65  thf('109', plain, (~ (l1_orders_2 @ sk_B_2)),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '108'])).
% 0.46/0.65  thf('110', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_l1_waybel_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) =>
% 0.46/0.65       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.46/0.65  thf('111', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i]:
% 0.46/0.65         (~ (l1_waybel_0 @ X23 @ X24)
% 0.46/0.65          | (l1_orders_2 @ X23)
% 0.46/0.65          | ~ (l1_struct_0 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.46/0.65  thf('112', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['110', '111'])).
% 0.46/0.65  thf('113', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('114', plain, ((l1_orders_2 @ sk_B_2)),
% 0.46/0.65      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.65  thf('115', plain, ($false), inference('demod', [status(thm)], ['109', '114'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
